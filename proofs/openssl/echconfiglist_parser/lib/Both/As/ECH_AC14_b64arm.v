(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9
  ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_AC7_biofreeint ECH_ARostr ECH_ALibMid ECH_AC11_fail
  ECH_AKitS ECH_AC12_addstr ECH_AC13 ECH_AC14_kit ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_b64arm_seg ECH_AC14_entry_seg
  ECH_AStmt_C14 F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition bf_fresh2 (R : b64frep) (nx : Z) : b64frep := mkBF 256 0 0 nx 0 (bf_ctx R) (bf_enc R) (bf_id R) (bf_cid R) (bf_eid R).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma b64r_loop_rv : forall fuel rest d ret outl acc used,
  0 <= outl -> Z.of_nat (length acc) = ret ->
  (br_rv (b64r_loop fuel rest d ret outl acc used) = Z.of_nat (length (br_out (b64r_loop fuel rest d ret outl acc used)))
   \/ (br_rv (b64r_loop fuel rest d ret outl acc used) = -1 /\ br_out (b64r_loop fuel rest d ret outl acc used) = []))
  /\ Z.of_nat (length (br_out (b64r_loop fuel rest d ret outl acc used))) <= ret + outl.
Proof.
  induction fuel as [|fuel IH]; intros rest d ret outl acc used OL LA.
  - cbn [b64r_loop]. destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
    + split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
    + split; [left; symmetry; exact LA| lia].
  - cbn [b64r_loop]. destruct (Z.leb_spec outl 0) as [E0|E0]; [cbn [br_rv br_out]; split; [left; symmetry; exact LA| lia]|].
    destruct rest as [|c rest'].
    + destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
      * destruct (decode_final_rv d <? 0); cbn [br_rv br_out].
        -- split; [| lia]. right. split; [reflexivity|]. destruct acc; [reflexivity| cbn in LA; lia].
        -- split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
      * split; [left; symmetry; exact LA| lia].
    + cbv zeta. set (r := decode_update d (firstn 1024 (c :: rest'))). clearbody r.
      destruct (dr_rv r <? 0); cbn [br_rv br_out].
      * destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
        -- split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
        -- split; [left; symmetry; exact LA| lia].
      * set (i := Z.min (Z.of_nat (length (dr_out r))) outl).
        assert (LI : Z.of_nat (length (acc ++ firstn (Z.to_nat i) (dr_out r))) = ret + i).
        { rewrite length_app, length_firstn. subst i. rewrite Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by lia. lia. }
        destruct (dr_rv r =? 0); cbn [br_rv br_out].
        -- destruct (Z.eqb_spec (ret + i) 0) as [E|E]; cbn [br_rv br_out].
           ++ split; [| lia]. destruct (acc ++ firstn (Z.to_nat i) (dr_out r)); [left; reflexivity| cbn in LI; lia].
           ++ split; [left; symmetry; exact LI| lia].
        -- destruct (IH (skipn 1024 (c :: rest')) (dr_d r) (ret + i) (outl - i) (acc ++ firstn (Z.to_nat i) (dr_out r)) (used + length (firstn 1024 (c :: rest')))%nat
                       ltac:(lia) LI) as [K1 K2].
           split; [exact K1| lia].
Qed.
Lemma b64_read_rv : forall txt outl, 0 <= outl ->
  (br_rv (b64_read_spec txt outl) = Z.of_nat (length (br_out (b64_read_spec txt outl)))
   \/ (br_rv (b64_read_spec txt outl) = -1 /\ br_out (b64_read_spec txt outl) = []))
  /\ Z.of_nat (length (br_out (b64_read_spec txt outl))) <= outl.
Proof. intros txt outl OL. unfold b64_read_spec. pose proof (b64r_loop_rv (S (S (length txt))) txt [] 0 outl [] 0%nat OL eq_refl) as K. rewrite Z.add_0_l in K. exact K. Qed.


Lemma sh_nsh_sub : forall B k A n, 0 <= B -> B mod 16 = 0 -> B <= A -> A + n <= B + k -> 0 <= n -> sh A + nsh n <= sh B + nsh k.
Proof. intros B k A n HB HM HA HN N0. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma ENCCTX_rebase : forall L L' m0 e d pid, ENCCTX H L m0 e d pid -> In (pid, e, ENCCTX_SIZE) L' -> ENCCTX H L' m0 e d pid.
  Proof.
    intros L L' m0 e d pid (raw & line & K1 & K2 & K3 & K4 & K5 & K6 & K7) IN. exists raw, line.
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact IN|]. split; [exact K6| exact K7].
  Qed.
  (* [comment removed for export] *)
  Lemma FX_at : forall (X : list (Z * Z)) (TB : list block) (b : block) (q sz : Z),
    (forall b, In b TB -> avoids X (blk_addr b) (blk_size b)) ->
    In b TB -> blk_addr b <= q -> q + sz <= blk_addr b + blk_size b -> 0 <= sz -> avoids X q sz.
  Proof. intros X TB b q sz FX IN LOQ HIQ SZ. eapply avoids_sub; [exact (FX _ IN)| exact LOQ| exact HIQ]. Qed.
  Lemma ENCCTX_xpresX : forall L L' SP X m1 m2 e d pid, ENCCTX H L m1 e d pid -> xpres H L' SP X m1 m2 -> In (pid, e, ENCCTX_SIZE) L' ->
    avoids X e ENCCTX_SIZE -> ENCCTX H L m2 e d pid.
  Proof.
    intros L L' SP X m1 m2 e d pid (raw & line & K1 & K2 & K3 & K4 & K5 & K6 & K7) XP IN FX. exists raw, line.
    split; [exact K1|]. split; [exact K2|]. split; [| split; [exact K4| split; [exact K5| split; [exact K6| exact K7]]]].
    eapply (xpres_rw_cells' H); [exact XP| exact K3| | cbn [cells_size csize Nat.add length]; unfold ENCCTX_SIZE in FX; exact FX].
    right; right; left. exists (pid, e, ENCCTX_SIZE). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENCCTX_SIZE. lia.
  Qed.
  Lemma B64F_used_xpres : forall L L' SP X m1 m2 a' Rx, B64F_used H L m1 a' Rx -> xpres H L' SP X m1 m2 ->
    In (bf_id Rx, a', BIO_SIZE) L' -> In (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE) L' ->
    avoids X a' BIO_SIZE -> avoids X (bf_ctx Rx) B64CTX_SIZE -> B64F_used H L m2 a' Rx.
  Proof.
    intros until Rx. intros (BC & (hdr & junk & elen & LH & LJ & EL & CJ) & REST) XP I1 I2 F1 F2. split; [| split; [exists hdr, junk, elen; split; [exact LH| split; [exact LJ| split; [exact EL|]]]| exact REST]].
    - eapply (xpres_rw_cells' H); [exact XP| exact BC| | unfold bio_cells; cbn [cells_size csize Nat.add length]; unfold BIO_SIZE in F1; exact F1].
      right; right; left. exists (bf_id Rx, a', BIO_SIZE). split; [exact I1|]. unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply (xpres_rw_cells' H); [exact XP| exact CJ| | unfold b64ctx_used_cells; cbn [cells_size csize Nat.add length]; unfold B64CTX_SIZE in F2; exact F2].
      right; right; left. exists (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE). split; [exact I2|]. unfold b64ctx_used_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold B64CTX_SIZE. lia.
  Qed.
  Lemma B64F_used_rebase : forall L L' m0 a' Rx, B64F_used H L m0 a' Rx -> (forall b, In b (blocks_B64F a' Rx) -> In b L') -> B64F_used H L' m0 a' Rx.
  Proof.
    intros L L' m0 a' Rx (BC & CX & (I1 & I2 & I3 & REST)) SUB. split; [exact BC|]. split; [exact CX|].
    split; [apply SUB; left; reflexivity|]. split; [apply SUB; right; left; reflexivity|]. split; [apply SUB; right; right; left; reflexivity| exact REST].
  Qed.

  (* [comment removed for export] *)
  Definition chainBT (TB : list block) (a mb2 : Z) (FBl MBl : list block) (m0 : mem) : Prop :=
    exists (R9 : b64frep) (d9 : list Z) (M9 : membio),
         B64F_used H TB m0 a R9 /\ blocks_B64F a R9 = FBl /\ bf_next R9 = mb2 /\ ENCCTX H TB m0 (bf_enc R9) d9 (bf_eid R9) /\ B64F_apart a R9 /\ B64F_shad m0 a R9
      /\ MEMBIO H TB m0 mb2 M9 /\ blocks_MEMBIO mb2 M9 = MBl /\ mb_next M9 = 0 /\ MEMBIO_apart mb2 M9 /\ MEMBIO_shad m0 mb2 M9.
  Lemma chainBT_frame : forall FBl MBl a mb2 (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
    chainBT (FBl ++ MBl) a mb2 FBl MBl m1 -> xpres H L SP X m1 m2 -> (forall b, In b (FBl ++ MBl) -> In b L) -> aceil <= SP ->
    (forall b, In b (FBl ++ MBl) -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    mem_inv asegs m2 -> chainBT (FBl ++ MBl) a mb2 FBl MBl m2.
  Proof.
    intros until m2. intros (R9 & d9 & M9 & BU & BLK & NX & EC & BAP & BSH & MB & MBK & MNX & MAP & MSH) XP SUB CE FX MI2. exists R9, d9, M9.
    pose proof BU as (_ & _ & (I1 & I2 & I3 & RG1 & RG2 & RG3 & _)).
    pose proof RG1 as (_ & _ & Z1 & _ & E1 & _). pose proof RG2 as (_ & _ & Z2 & _ & E2 & _). pose proof RG3 as (_ & _ & Z3 & _ & E3 & _).
    assert (FXa : forall b, In b (FBl ++ MBl) -> avoids X (blk_addr b) (blk_size b)) by (intros b Hb; exact (proj1 (FX b Hb))).
    split; [| split; [exact BLK| split; [exact NX| split; [| split; [exact BAP| split; [| split; [| split; [exact MBK| split; [exact MNX| split; [exact MAP|]]]]]]]]]].
    - eapply B64F_used_xpres; [exact BU| exact XP| apply SUB; exact I1| apply SUB; exact I2| |].
      + exact (FX_at X _ (bf_id R9, a, BIO_SIZE) a BIO_SIZE FXa I1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold BIO_SIZE; lia)).
      + exact (FX_at X _ (bf_cid R9, bf_ctx R9, B64CTX_SIZE) (bf_ctx R9) B64CTX_SIZE FXa I2 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold B64CTX_SIZE; lia)).
    - pose proof EC as (_ & _ & _ & _ & _ & _ & IE & _).
      eapply ENCCTX_xpresX; [exact EC| exact XP| apply SUB; exact IE|].
      exact (FX_at X _ (bf_eid R9, bf_enc R9, ENCCTX_SIZE) (bf_enc R9) ENCCTX_SIZE FXa IE ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold ENCCTX_SIZE; lia)).
    - destruct BSH as (S1' & S2' & S3'). pose proof EC as (_ & _ & _ & _ & _ & _ & IE & RGE & _). pose proof RGE as (_ & _ & _ & _ & EE & _).
      split; [| split].
      + eapply (addressable_xpres_blkX H); [apply SUB; exact I1| unfold AAPP_HI; acb; lia| exact S1'| exact XP| exact (proj2 (FX _ I1))].
      + eapply (addressable_xpres_blkX H); [apply SUB; exact I2| unfold AAPP_HI; acb; lia| exact S2'| exact XP| exact (proj2 (FX _ I2))].
      + rewrite <- BLK in SUB, FX. eapply (addressable_xpres_blkX H); [apply SUB; right; right; left; reflexivity| unfold AAPP_HI; acb; lia| exact S3'| exact XP| exact (proj2 (FX _ ltac:(right; right; left; reflexivity)))].
    - eapply (AMEMBIO_xpres H _ L SP X m1 m2); [exact MB| intros b Hb; apply SUB; rewrite MBK in Hb; apply in_or_app; right; exact Hb| exact XP|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb. rewrite MBK in Hb. exact (proj1 (Forall_forall _ _) (FXa b ltac:(apply in_or_app; right; exact Hb)) iv Hiv).
    - destruct MSH as (T1 & T2 & T3 & T4). pose proof MB as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & Q1 & Q2 & Q3 & Q4 & _).
      pose proof Q1 as (_ & _ & _ & _ & U1 & _). pose proof Q2 as (_ & _ & _ & _ & U2 & _). pose proof Q3 as (_ & _ & _ & _ & U3 & _). pose proof Q4 as (_ & _ & _ & _ & U4 & _).
      rewrite <- MBK in SUB, FX. unfold blocks_MEMBIO in SUB, FX. acb.
      split; [| split; [| split]].
      + eapply (addressable_xpres_blkX H); [apply SUB; apply in_or_app; right; left; reflexivity| unfold AAPP_HI; lia| exact T1| exact XP| exact (proj2 (FX _ ltac:(apply in_or_app; right; left; reflexivity)))].
      + eapply (addressable_xpres_blkX H); [apply SUB; apply in_or_app; right; right; left; reflexivity| unfold AAPP_HI; lia| exact T2| exact XP| exact (proj2 (FX _ ltac:(apply in_or_app; right; right; left; reflexivity)))].
      + eapply (addressable_xpres_blkX H); [apply SUB; apply in_or_app; right; right; right; left; reflexivity| unfold AAPP_HI; lia| exact T3| exact XP| exact (proj2 (FX _ ltac:(apply in_or_app; right; right; right; left; reflexivity)))].
      + eapply (addressable_xpres_blkX H); [apply SUB; apply in_or_app; right; right; right; right; left; reflexivity| unfold AAPP_HI; lia| exact T4| exact XP| exact (proj2 (FX _ ltac:(apply in_or_app; right; right; right; right; left; reflexivity)))].
  Qed.
  Lemma blocks_B64F_facts : forall a' Rx, Z.of_nat (length (blocks_B64F a' Rx)) = 3 /\ lb_bytes (blocks_B64F a' Rx) = B64F_BYTES.
  Proof. intros a' Rx. unfold blocks_B64F, B64F_BYTES. cbn. split; reflexivity. Qed.
End CH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le8_of_bytes14 : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
Proof.
  intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
  change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by (cbn in B; clear - B B0; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma fframe_to2 : forall m q j1 rb j2 fpq ffq,
  rw_cells asegs m ffq (arp_fframe q j1 rb j2 fpq) ->
  exists (tpl : Z) (j24 tpb j128 : list byte), (exists lb : byte, rw_cells asegs m ffq (arp_fframe2 q tpl j24 lb tpb j128 rb j2 fpq)) /\ 0 <= tpl < 2^64.
Proof.
  intros m q j1 rb j2 fpq ffq FR. unfold arp_fframe in FR.
  pose proof (rw_cells_split_CB asegs m ffq [C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz q)] 2224 j1
                [C8 (wz rb); CB 1824 j2; C8 (wz fpq)] [8%nat; 24%nat; 1%nat; 2063%nat; 128%nat] FR ltac:(reflexivity)) as FR2.
  cbn [mk_CB_cells app] in FR2.
  assert (L1 : length j1 = 2224%nat /\ length j2 = 1824%nat) by (pose proof FR as [[WF _] _]; cbn in WF; tauto). destruct L1 as [L1 L2].
  destruct (le8_of_bytes14 (firstn 8 j1) ltac:(rewrite length_firstn; lia)) as [w Hw].
  assert (E1 : exists lb : byte, firstn 1 (skipn 24 (skipn 8 j1)) = [lb]).
  { destruct (skipn 24 (skipn 8 j1)) as [|b t] eqn:Es; [exfalso| exists b; reflexivity].
    apply (f_equal (@length byte)) in Es. rewrite !length_skipn in Es. cbn in Es. lia. }
  destruct E1 as [lb Hlb].
  exists (bv_unsigned w), (firstn 24 (skipn 8 j1)), (firstn 2063 (skipn 1 (skipn 24 (skipn 8 j1)))), (firstn 128 (skipn 2063 (skipn 1 (skipn 24 (skipn 8 j1))))).
  split; [exists lb| apply aword_range].
  unfold arp_fframe2. eapply arw_cells_recut; [exact FR2| cbn; repeat split; rewrite ?length_firstn, ?length_skipn; lia|].
  cbn [cells_bytes cbytes app]. unfold wz. rewrite Z_to_bv_bv_unsigned. change (cbytes (C8 w)) with (le8 w). rewrite Hw, Hlb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma asegs_find_segment_none_high14 : forall a n, 1 <= n -> 12599296 <= a -> find_segment asegs a n = None.
Proof.
  intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 1593344)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1658880 a); destruct (Z.leb_spec (a + n) (1658880 + 4046848)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 5705728 a); destruct (Z.leb_spec (a + n) (5705728 + 495616)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 6201344 a); destruct (Z.leb_spec (a + n) (6201344 + 6397952)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_same_raw_hi14 : forall m m' A cs a,
  rw_cells asegs m A cs -> rw_cells asegs m' A cs -> AIMG_TOP <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof.
  intros m m' A cs a [[W1 B1] X1] [[W2 B2] X2] TOP HI Ha.
  pose proof (cells_bytes_length cs W1) as CL.
  destruct B1 as (HA & HL & R1). destruct B2 as (_ & _ & R2). destruct X2 as (_ & _ & WW2).
  split.
  - specialize (R1 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)). specialize (R2 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)).
    rewrite Z2Nat.id in R1, R2 by lia. replace (A + (a - A)) with a in R1, R2 by lia.
    unfold mrd in R1, R2. unfold AIMG_TOP in TOP.
    assert (SR : seg_rom asegs (wa a) = None).
    { unfold seg_rom, memory_read. unfold wa. rewrite unsigned_lit by lia. rewrite asegs_find_segment_none_high14 by lia. reflexivity. }
    destruct (m (wa a)) as [b1|]; destruct (m' (wa a)) as [b2|]; rewrite ?SR in R1, R2; congruence.
  - intros _. replace a with (A + (a - A)) by lia. apply WW2. lia.
Qed.

Lemma rw_cells_CB_bytes_at14 : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs /\ length bs = n.
Proof.
  intros segs m A n bs [[WF B] W]. cbn in WF. destruct WF as [L _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. split; assumption.
Qed.

Section CH2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  (* [comment removed for export] *)
  Lemma xpres_drop_same14 : forall LB SP X Y m m',
    xpres H LB SP (X ++ Y) m m' -> (forall q, rin_ivs X q -> m' (wa q) = m (wa q) /\ (wview asegs m (wa q) <> None -> wview asegs m' (wa q) <> None)) ->
    xpres H LB SP Y m m'.
  Proof.
    intros LB SP X Y m m' XP SAME q Hq [HC HY].
    assert (D : rin_ivs X q \/ ~ rin_ivs X q).
    { clear. induction X as [|[lo hi] X IH]; cbn; [right; tauto|]. destruct (Z_le_gt_dec lo q); destruct (Z_lt_ge_dec q hi); destruct IH as [IH|IH]; try (left; lia); try (left; right; exact IH); right; intros [K|K]; [lia| exact (IH K)| lia| exact (IH K)|lia|exact (IH K)]. }
    destruct D as [D|D]; [exact (SAME q D)|]. apply XP; [exact Hq|]. split; [exact HC|].
    intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (D K)| exact (HY K)].
  Qed.
  (* [comment removed for export] *)
  Lemma ENCCTX_transport14 : forall W m m' LB a d p,
    munch W m m' -> wmono asegs m m' -> disjoint_from W a 92 -> ENCCTX H LB m a d p -> ENCCTX H LB m' a d p.
  Proof.
    intros W m m' LB a d p MU WM DJ (raw & line & L & MD & RC & LN & IN & RB & DI).
    exists raw, line. split; [exact L|]. split; [exact MD|]. split; [| exact (conj LN (conj IN (conj RB DI)))].
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact DJ.
  Qed.
  (* [comment removed for export] *)
  Lemma outside_not_rin14 : forall W a, outside W a -> rin_ivs W a -> False.
  Proof. induction W as [|[l h] W IH]; intros a O R; cbn in O, R; [exact R|]. destruct O as [O1 O2]. destruct R as [R|R]; [exact (O1 R)| exact (IH a O2 R)]. Qed.
  Lemma munch_incl : forall W W' m m', munch W m m' -> (forall a, rin_ivs W a -> rin_ivs W' a) -> munch W' m m'.
  Proof.
    intros W W' m m' MU INCL. eapply munch_weaken; [| exact MU]. intros a Oa. apply ECH_AC14_b2b.outside_of_not_rin. intros R. exact (outside_not_rin14 _ _ Oa (INCL _ R)).
  Qed.
  (* [comment removed for export] *)
  Lemma B64F_fresh_mono : forall L L' m a R, B64F_fresh H L m a R -> (forall b, In b (blocks_B64F a R) -> In b L') -> B64F_fresh H L' m a R.
  Proof.
    intros L L' m a R (BC & CJ & (I1 & I2 & I3 & REST) & FL & RT & NR) SUB.
    split; [exact BC|]. split; [exact CJ|]. split; [| exact (conj FL (conj RT NR))].
    split; [apply SUB; left; reflexivity|]. split; [apply SUB; right; left; reflexivity|]. split; [apply SUB; right; right; left; reflexivity| exact REST].
  Qed.
  Lemma B64F_fresh_xpres0 : forall L L' SP m1 m2 a R, B64F_fresh H L m1 a R -> xpres H L' SP [] m1 m2 ->
    In (bf_id R, a, BIO_SIZE) L' -> In (bf_cid R, bf_ctx R, B64CTX_SIZE) L' -> B64F_fresh H L m2 a R.
  Proof.
    intros L L' SP m1 m2 a R (BC & (cj & CJL & CJ) & BB & REST) XP I1 I2. split; [| split; [exists cj; split; [exact CJL|]| exact (conj BB REST)]].
    - eapply (xpres_rw_cells' H); [exact XP| exact BC| | apply Forall_nil]. right; right; left. exists (bf_id R, a, BIO_SIZE). split; [exact I1|].
      unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply (xpres_rw_cells' H); [exact XP| exact CJ| | apply Forall_nil]. right; right; left. exists (bf_cid R, bf_ctx R, B64CTX_SIZE). split; [exact I2|].
      unfold b64ctx_fresh_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold B64CTX_SIZE. lia.
  Qed.
End CH2.
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let SM6 : stack_malloc_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let SF6 : stack_free_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SSF8 : set_shadow_f8_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))))).
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)).
  Hypotheses (VIS0 : as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
             (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo) (SSH : STORE_shad m st S)
             (MBO : MEMBIO H LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (MSH : MEMBIO_shad m mb R) (PAY : PAYLOAD_shad m R)
             (DS : bytes_at asegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (PAYL2 : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : as_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : as_AKREL H s (mkCfg msF mo))
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H)
             (AUX : as_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk asegs m lo (bv_unsigned sp)) (CEIL : aceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M) (ST0 : stack0 m lo (bv_unsigned sp))
             (ERR : rw_cells asegs m (errno_addr tp) [C4 errv]) (MI : mem_inv asegs m) (TP : tp = Z_to_bv 64 ATP) (AC : ACONST m)
             (MCO : mid_closed_ok H M)
             (RFS : as_RFS H LF m) (LFB : (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) (ATH : athr_cells m)
             (CHN : as_chain H m (bv_unsigned s0) CH) (CHB : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
             (PF : pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) (ALW : READCFG_COST H M <= as_AL H s)
             (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation S1c := (S1 sp).
  Local Notation KGc := (KG sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds).
  Local Notation XFc := (XF M st mb R).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation CH1c := (CH1 ra sp CH).
  Local Notation LF1c := (LF1 LF).
  Local Notation XSFc := (XSF H).
  Local Notation LEDGERc := (LEDGER H s).
  Local Notation pf_sitec := (pf_site H PF9new PF9free ra sp M CH PF).
  Local Notation rp_okKc := (rp_okK H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  (* [comment removed for export] *)
  Local Notation "'RCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).

  (* [comment removed for export] *)
  Local Notation AFWc := (AFW H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B R ds CH).
  Local Notation SLOTSc := (SLOTS sp st).
  Local Notation rp_b64Kc := (rp_b64K H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  Local Notation "'DCW' f" := (f H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCS' f" := (f H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCB' f" := (f H PF9free ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).

  (* [comment removed for export] *)
  Hypothesis NEWMB : newmembuf_stmt H.
  Hypothesis BNEW : bionew_b64_stmt H.
  Hypothesis BPUSH : biopush_stmt H.
  Hypothesis BREAD : bioread_b64_stmt H.
  Hypothesis BFALL : biofreeall_stmt H.
  Hypothesis PF9NEW : forall xq, PF9new (CtxReady xq) = PF_bionew_b64 xq.
  Hypothesis PF9FREE : PF9free = PF_biofreeall.
  (* [comment removed for export] *)
  Hypothesis ERRL : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block) (BT : mem -> Prop)
                          (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte),
      1 <= mb_len R <= nA /\ nA <= 512 * 3 -> 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      mb_static R R' -> mb_pos R' = mb_len R -> 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
          BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
          (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> BT m2) ->
      fresh_frame H LF 6 ff fp ->
     (DCB btfree_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 ->
     (DCS rp_errl_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5.
  Hypothesis RPFLAT : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block) (BT : mem -> Prop)
                            (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte),
      1 <= mb_len R <= nA /\ nA <= 512 * 3 -> 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      mb_static R R' -> mb_pos R' = mb_len R -> 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
          BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
          (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> BT m2) ->
      fresh_frame H LF 6 ff fp ->
     (DCB btfree_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 ->
     (DCS rp_flat_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5.

  Local Ltac img_static := unfold A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.

  (* [comment removed for export] *)
  Lemma rc_facts_c :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0c /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0c -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0c)
    /\ List.NoDup (map blk_id L0c) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0c)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 464 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 448 /\ bv_unsigned sp < 2^64.
  Proof. exact (RCI rc_facts). Qed.
  Lemma dc_smoke : forall p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m' s',
    (DCW adwkG) p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s' ->
    (DCW adwk) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 [] NB S' M' LE = (DCW adwk) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 [] NB S' M' LE.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CW (Lx : list block) (p : bptr) (A nA : Z) (R' : membio) (ff fp : Z) (fk1 fk2 jg e5 : list byte) (n um uf : Z) (m' : mem) (s' : as_St H) : Prop :=
       as_RHEAP H s' (Lx ++ (p, A, nA) :: L0c) m'
    /\ MEMBIO H LB m' mb R' /\ mb_static R R' /\ mb_pos R' = mb_len R /\ 1 <= mb_len R <= nA /\ nA <= 512 * 3 /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN
    /\ bytes_at asegs m' (mb_buf R) ds /\ bytes_at asegs m' A ds
    /\ (exists junk, rw_cells asegs m' A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) junk]) /\ addressable m' A nA
    /\ SLOTSc m' ff A /\ rw_cells asegs m' (S1c + 344) [CB (Z.to_nat KGc) jg] /\ rw_cells asegs m' (bv_unsigned sp + -104) SAVESc
    /\ fresh_frame H LF 6 ff fp
    /\ rw_cells asegs m' ff (arp_fframe S1c fk1 n fk2 fp)
    /\ rw_cells asegs m' (Z.shiftr ff 3 + ASHB) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0xf8) e5)
    /\ as_RFS H (LF1c ff fp) m'
    /\ (exists errv', rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'])
    /\ as_rauxv_ok H m' B /\ LIBMID LIB m' M
    /\ rw_cells asegs m' st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ addressable m' st STORE_SIZE
    /\ MEMBIO_shad m' mb R' /\ accessible m' (mb_buf R) (mb_len R)
    /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo S1c /\ stack0 m' lo (bv_unsigned sp)
    /\ as_chain H m' (bv_unsigned sp) CH1c
    /\ (exists XSq, Forall (fs_scratch H LF) XSq /\ (forall q, rin_ivs (XSFc ff fp) q -> rin_ivs XSq q) /\ xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m')
    /\ LEDGERc s' um uf.

  Lemma cw_of_afw : forall p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s',
    AFWc [] p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s' -> CW [] p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s'.
  Proof.
    clear. intros until s'. intros FW.
    pose proof FW as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & JK1 & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & ERR1 & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    unfold CW. repeat match goal with |- _ /\ _ => split end; try assumption.
    1-2: clear - LR; lia.
    exists (XSFc ff fp). split; [apply (fs_scratch_of_fresh H); exact FRESH|]. split; [intros q Hq; exact Hq|].
    eapply (xpres_weaken H); [exact XA1| apply Z.le_refl| intros b Hb; exact Hb|].
    intros q Hq. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; exact Hq| right]. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq.
  Qed.

  (* [comment removed for export] *)
  Definition cwin (Lx : list block) (ff fp : Z) (iv : Z * Z) : Prop :=
       (lo <= fst iv /\ snd iv <= S1c)
    \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
    \/ fs_scratch H (LF1c ff fp) iv.

  (* [comment removed for export] *)
  Lemma cw_ws : forall Lx p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' m2 W0 XS,
    CW Lx p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' ->
    munch (W0 ++ XS) m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c -> as_RFS H (LF1c ff fp) m2 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W0 ->
    Forall (fs_scratch H (LF1c ff fp)) XS ->
    CW Lx p A nA R' ff fp fk1 fk2 jg e5 n um uf m2 s1'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRL RPFLAT.
    intros until XS. intros Wd MU WM MI2 AC2 STK2 RFS2 FW00 FXS.
    set (W := W0 ++ XS) in MU.
    assert (FW0 : Forall (cwin Lx ff fp) W).
    { subst W. apply Forall_app. split; [eapply Forall_impl; [| exact FW00]; cbn beta; intros iv [K|K]; [left; exact K| right; left; exact K]| eapply Forall_impl; [| exact FXS]; cbn beta; intros iv K; right; right; exact K]. }
    pose proof Wd as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (INF : In (6, ff, fp) (LF1c ff fp)) by (left; reflexivity).
    set (Lall := Lx ++ (p, A, nA) :: L0c) in *.
    set (Lq := (p, A, nA) :: L0c) in *.
    assert (INX : forall b, In b Lx -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; left; exact Hb).
    assert (IN0 : forall b, In b Lq -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; exact Hb).
    assert (SQ : forall b, In b LB -> In b Lq) by (intros b Hb; subst Lq; right; exact (SUB0 _ Hb)).
    pose proof (ah_nodup H HH _ _ _ HP1) as ND. destruct (nd_app _ _ ND) as [D2 _].
    assert (BRS : forall b, In b Lall -> ablock_range H (blk_addr b) (blk_size b)) by (intros b Hb; exact (ah_blocks H HH _ _ _ _ HP1 Hb)).
    assert (DISJ : forall b b', In b Lall -> In b' Lall -> blk_id b <> blk_id b' -> blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
      by (intros b b' Hb Hb' NE; exact (ah_disj H HH _ _ _ _ _ HP1 Hb Hb' NE)).
    (* [comment removed for export] *)
    assert (CW0 : Forall (aclient_write_ok H Lall) W).
    { eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b & Hb & K1 & K2)|K]]; [left; clear - K CEIL; lia| | exact (fs_scratch_write_ok H (LF1c ff fp) Lall iv K)].
      right; right; left. exists b. split; [exact (INX _ Hb)| split; [exact K1| exact K2]]. }
    (* [comment removed for export] *)
    assert (BWq : forall b Aq nq, In b Lq -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> disjoint_from W Aq nq /\ Forall (winX Aq nq) W).
    { intros b Aq nq Hb HA HB N0. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). pose proof (aapp_not_shadowland _ _ E7) as NS.
      assert (ABx : forall b', In b' Lx -> blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b).
      { intros b' Hb'. apply (DISJ b b' (IN0 _ Hb) (INX _ Hb')). intros EQ. exact (D2 _ _ Hb' Hb (eq_sym EQ)). }
      split.
      - apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b' & Hb' & K1 & K2)|K]].
        + left. clear - K E5 HB CEIL. lia.
        + pose proof (ABx b' Hb'). clear - H0 K1 K2 HA HB N0. lia.
        + exact (djF_inv _ _ _ _ (dj_scratch_placed H HH _ _ _ _ _ Aq nq RFS1 (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) (BRS b (IN0 _ Hb)) HA HB) (or_introl eq_refl)).
      - eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b' & Hb' & K1 & K2)|K]]; unfold winX.
        + right; left. unfold AHI_LO. clear - K CEIL ACB. lia.
        + pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'.
          assert (SB0 : ASHADOW_BASE <= sh Aq) by (unfold sh; clear - E1 HA; Z.div_mod_to_equations; lia).
          pose proof (sh_nsh_high Aq nq ltac:(clear - E1 HA; lia) N0 ltac:(unfold AAPP_HI; clear - E5 HB ACB; lia)) as SNH.
          unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' SNH SB0. rewrite ?ASHADOW_BASE_val in *. lia.
        + right; right. exact (djF_inv _ _ _ _ (dj_scratch_placed_sh H HH _ _ _ _ _ (sh Aq) (nsh nq) RFS1 (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) (BRS b (IN0 _ Hb)) (sh_mono _ _ HA) (sh_nsh_sub (blk_addr b) (blk_size b) Aq nq ltac:(clear - E1; lia) E2 HA HB N0)) (or_introl eq_refl)). }
    (* [comment removed for export] *)
    assert (DJS : forall Aq nq, S1c <= Aq -> disjoint_from W Aq nq).
    { intros Aq nq HA. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b & Hb & K1 & K2)|K]].
      - right. clear - K HA. lia.
      - pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _). clear - K2 E5 HA AS1. lia.
      - exact (djF_inv _ _ _ _ (dj_scratch_hi H HH _ _ _ Aq nq RFS1 (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) ltac:(clear - HA AS1; lia)) (or_introl eq_refl)). }
    assert (DJF : disjoint_from W ff 4096).
    { apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b & Hb & K1 & K2)|K]].
      - clear - K CEIL FQ6 AF2. lia.
      - pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & E6 & _). unfold AFS_SIZE in E6. clear - K1 K2 E6 FQ5 FQ6. lia.
      - exact (djF_inv _ _ _ _ (dj_scratch_live H HH _ _ _ 6 ff fp ff 4096 RFS1 INF (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) ltac:(apply Z.le_refl) ltac:(change (fsz 6) with 4096; apply Z.le_refl)) (or_introl eq_refl)). }
    assert (DJSH : disjoint_from W (sh ff) 512).
    { apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
      pose proof (sh_mono (ff + 4096) _ FQ6) as SYU. pose proof (sh_mono _ _ AF2) as SYA. intros iv [K|[(b & Hb & K1 & K2)|K]].
      - clear - K CEIL SY8 SYU SYA SHC. lia.
      - pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'.
        pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold AIMG_TOP in W1. rewrite S0 in W1.
        unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' SYL SY8 SYU SYA W1 W3 SHC. lia.
      - exact (djF_inv _ _ _ _ (dj_scratch_live_sh H HH _ _ _ 6 ff fp (sh ff) 512 RFS1 INF (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) ltac:(apply Z.le_refl) ltac:(change (fshn 6) with 512; apply Z.le_refl)) (or_introl eq_refl)). }
    assert (DJE : disjoint_from W (errno_addr (Z_to_bv 64 ATP)) 4).
    { apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [K|[(b & Hb & K1 & K2)|K]].
      - left. clear - K ERNG CEIL ACB. lia.
      - pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & E4 & _). unfold AIMG_TOP in E4. clear - K1 ERNG E4. lia.
      - exact (djF_inv _ _ _ _ (dj_scratch_img H HH _ _ _ (errno_addr (Z_to_bv 64 ATP)) 4 RFS1 (@Forall_cons _ _ iv [] K (@Forall_nil _ _)) ltac:(unfold AIMG_TOP; clear - ERNG; lia)) (or_introl eq_refl)). }
    assert (MBLB : forall b, In b (blocks_MEMBIO mb R') -> In b LB).
    { intros b Hb. rewrite (mb_static_blocks mb R R' MST) in Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    (* [comment removed for export] *)
    assert (SCF : forall iv, fs_scratch H (LF1c ff fp) iv -> fswin H iv).
    { intros iv [->|(k & ff' & fp' & FF & E)]; [right; left; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE; clear; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (Kk & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). pose proof (fsz_pos k ltac:(clear - Kk; lia)) as FZ.
      destruct E as [-> |[-> | ->]]; cbn [fst snd].
      - right; left. cbn [fst snd]. unfold AFS_HDR in P5. clear - P5 P6 FZ. lia.
      - right; left. cbn [fst snd]. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. clear - P3 P4. lia.
      - right; right. cbn [fst snd]. pose proof (sh_mono _ _ ltac:(clear - P5; unfold AFS_HDR in P5; assert (as_FSB H <= ff') by lia; exact H0)) as SM1. pose proof (sh_mono _ _ P6) as SM2.
        assert (E8 : sh (ff' + fsz k) = sh ff' + fshn k) by (unfold fshn, fsz, sh; clear - M8; Z.div_mod_to_equations; nia). rewrite <- E8. clear - SM1 SM2. lia. }
    (* [comment removed for export] *)
    assert (XP : xpres H Lq (bv_unsigned sp) W m1 m2).
    { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa. }
    assert (XPall : xpres H Lall (bv_unsigned sp) W m1 m2).
    { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa. }
    pose proof (BRS _ (IN0 _ ltac:(left; reflexivity))) as (EA1 & EA2 & EA3 & EA4 & EA5 & EA6 & EA7). cbn [blk_addr blk_size fst snd] in EA1, EA2, EA3, EA4, EA5, EA6, EA7.
    pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof SBR as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7).
    assert (TAD : forall b Aq nq, In b Lq -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> addressable m1 Aq nq -> addressable m2 Aq nq).
    { intros b Aq nq Hb HA HB N0 AD. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - E1 HA; lia| unfold AAPP_HI; clear - E5 HB ACB; lia| exact (proj2 (BWq b Aq nq Hb HA HB N0))]. }
    unfold CW. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
    | |- as_RHEAP H _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU| exact WM| exact CW0]
    | |- 1 <= mb_len R => clear - LR; lia
    | |- mb_len R <= _ => clear - LR; lia
    | |- MEMBIO H LB _ mb _ =>
        eapply (AMEMBIO_munch H LB W m1 m2); [exact MBO1| exact MU| exact WM|];
        apply Forall_forall; intros iv Hiv; apply Forall_forall; intros b Hb; cbn beta;
        exact (djF_inv _ _ _ _ (proj1 (BWq b _ _ (SQ _ (MBLB _ Hb)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b (IN0 _ (SQ _ (MBLB _ Hb)))) as (_ & _ & E3 & _); exact E3))) Hiv)
    | |- bytes_at asegs _ (mb_buf R) ds =>
        destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]];
        eapply bytes_at_transport; [exact DSm1| exact MU|]; exact (proj1 (BWq (pD, mb_buf R, mb_len R) (mb_buf R) (Z.of_nat (length ds)) (SQ _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; rewrite DSL1; apply Z.le_refl) ltac:(clear; lia)))
    | |- bytes_at asegs _ _ ds =>
        eapply bytes_at_transport; [exact DSA1| exact MU|]; exact (proj1 (BWq (p, A, nA) A (Z.of_nat (length ds)) ltac:(left; reflexivity) ltac:(apply Z.le_refl) ltac:(cbn; clear - DSL1 LR; lia) ltac:(clear; lia)))
    | |- exists j, rw_cells asegs _ _ [CB _ ds; CB _ j] =>
        exists junk1; eapply rw_cells_transport; [exact JK1| exact MU| exact WM|];
        eapply (ECH_AKit.disjoint_from_sub W A nA); [exact (proj1 (BWq (p, A, nA) A nA ltac:(left; reflexivity) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) ltac:(clear - LR; lia)))| apply Z.le_refl| cbn [cells_size csize Nat.add]; clear - LR DSL1; lia| cbn [cells_size csize Nat.add]; clear - LR DSL1; lia]
    | |- addressable _ st STORE_SIZE => exact (TAD (es_id S, st, STORE_SIZE) st STORE_SIZE (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(unfold STORE_SIZE; clear; lia) SAD1)
    | |- addressable _ _ _ => exact (TAD (p, A, nA) A nA ltac:(left; reflexivity) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) EA3 ADA1)
    | |- SLOTS _ _ _ _ _ => eapply SLOTS_carry; [| exact SL1]; intros Aq cs RC HA; eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (DJS _ _ HA)]
    | |- rw_cells asegs _ (S1c + 344) _ => eapply rw_cells_transport; [exact GP1| exact MU| exact WM| apply DJS; clear; lia]
    | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => eapply rw_cells_transport; [exact SV1| exact MU| exact WM| apply DJS; clear - Q2; lia]
    | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) =>
        pose proof FRM1 as [[WF _] _]; cbn in WF; eapply rw_cells_transport; [exact FRM1| exact MU| exact WM|];
        eapply (ECH_AKit.disjoint_from_sub W ff 4096); [exact DJF| apply Z.le_refl| unfold arp_fframe; cbn [cells_size csize Nat.add length]; clear - WF; lia| clear; lia]
    | |- rw_cells asegs _ _ (arp_fshadow _ _ _ _ _ _ _ _ _) =>
        rewrite SHF in FSH1 |- *; pose proof FSH1 as [[WF _] _]; cbn in WF; eapply rw_cells_transport; [exact FSH1| exact MU| exact WM|];
        eapply (ECH_AKit.disjoint_from_sub W (sh ff) 512); [exact DJSH| apply Z.le_refl| unfold arp_fshadow; cbn [cells_size csize Nat.add length]; clear - WF; lia| clear; lia]
    | |- exists e, rw_cells asegs _ (errno_addr _) [C4 e] => exists errv1; eapply rw_cells_transport; [exact ERR1| exact MU| exact WM| exact DJE]
    | |- as_rauxv_ok H _ B => eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU| exact WM| exact CW0]
    | |- LIBMID LIB _ M =>
        eapply (LIBMID_xobj H HH s1' m1 LIB Lall (bv_unsigned sp) W [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_SIZE); (sh (as_FSB H), sh (as_FSB H + AFS_SIZE))] Lx m1 m2 M x);
          [exact HP1| exact LM1| exact CTX| exact XPall| intros b Hb; exact (IN0 _ (SQ _ (SUBL _ Hb)))| intros b Hb; apply IN0; subst Lq; right; unfold L0; apply in_or_app; left; exact Hb| exact INX| | |];
        [ intros b b' Hb Hb' EQ; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (D2 _ _ Hb' (SQ _ (SUBL _ Hb)) (eq_sym EQ))| exact (D2 _ _ Hb' ltac:(subst Lq; right; unfold L0; apply in_or_app; left; exact Hb) (eq_sym EQ))]
        | apply Forall_cons; [left; cbn [fst]; exact CEIL|]; apply Forall_cons; [right; left; cbn [fst snd]; split; apply Z.le_refl|]; apply Forall_cons; [right; right; cbn [fst snd]; split; apply Z.le_refl| apply Forall_nil]
        | intros a Ra; destruct (rin_ivs_In _ _ Ra) as (iv & Hiv & Riv); pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K; cbn beta in K;
          destruct K as [K|[(b & Hb & K1 & K2)|K]];
          [ right; cbn; left; clear - K Riv Q2 LO STK0; lia
          | left; exists b; split; [exact Hb| clear - K1 K2 Riv; lia]
          | right; destruct (SCF iv K) as [K'|[[K1 K2]|[K1 K2]]]; cbn;
            [ pose proof (fs_scratch_range H HH _ _ _ RFS1 K) as [_ [_ KU]]; exfalso; clear - K' KU Riv; lia
            | right; left; clear - K1 K2 Riv; lia
            | right; right; left; clear - K1 K2 Riv; lia ] ] ]
    | |- rw_cells asegs _ st _ =>
        eapply rw_cells_transport; [exact SC1| exact MU| exact WM|];
        exact (proj1 (BWq (es_id S, st, STORE_SIZE) st 24 (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(apply Z.le_refl) ltac:(cbn; unfold STORE_SIZE; apply Z.le_refl) ltac:(clear; lia)))
    | |- MEMBIO_shad _ mb _ =>
        destruct MSH1 as (X1 & X2 & X3 & X4); pose proof MBO1 as MBq; destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _);
        unfold MEMBIO_shad; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *;
        split; [| split; [| split]];
        [ eapply (TAD (mb_id R', mb, 128)); [apply SQ; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1]
        | eapply (TAD (mb_bbid R', mb_bb R', 16)); [apply SQ; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2]
        | eapply (TAD (mb_bmid R', mb_bm R', 32)); [apply SQ; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3]
        | eapply (TAD (mb_rpid R', mb_rp R', 32)); [apply SQ; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4] ]
    | |- accessible _ (mb_buf R) (mb_len R) =>
        destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]]; pose proof (BRS _ (IN0 _ (SQ _ PIN))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7); cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7;
        eapply accessible_transport; [exact PAYa1| exact MU|]; intros y Hy; apply outF; eapply Forall_impl; [| exact (proj2 (BWq (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) (SQ _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) E3))]; cbn beta;
        assert (SB0 : ASHADOW_BASE <= sh y) by (unfold sh; clear - E1 Hy; Z.div_mod_to_equations; lia);
        pose proof (sh_nsh_high y 1 ltac:(clear - E1 Hy; lia) ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - E5 Hy ACB; lia)) as SNH;
        assert (SYM : sh (mb_buf R) <= sh y /\ sh y + 1 <= sh (mb_buf R) + nsh (mb_len R)) by (unfold sh, nsh; clear - Hy E2; Z.div_mod_to_equations; lia);
        intros iv [K|[K|[K|K]]]; [right; clear - K SB0; lia| left; unfold nsh in SNH; clear - K SNH; lia| left; clear - K SYM; lia| right; clear - K SYM; lia]
    | |- stack0 _ lo _ =>
        eapply stack0_transport; [exact ST01| exact MU| exact WM|]; eapply Forall_impl; [| exact FW0]; cbn beta;
        intros iv [K|[(b & Hb & K1 & K2)|K]]; destruct iv as [l h]; cbn [fst snd] in *;
        [ apply stack0_ok_app; unfold AHI_LO; clear - K CEIL ACB; lia
        | pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & _ & E7'); eapply (stack0_ok_aapp _ _ _ _ E7'); [exact K1| exact K2]
        | exact (fs_scratch_stack0_ok H HH _ _ _ RFS1 K) ]
    | |- as_chain H _ _ _ =>
        eapply (achain_below H HH m1 m2 _ _ _ (bv_unsigned sp)); [exact CHN1| intros fp' ra' [E|Hin]; [injection E as <- <-; apply Z.le_refl| pose proof (CHB _ _ Hin) as CB'; clear - CB'; lia]| exact MU|];
        eapply Forall_impl; [| exact FW0]; cbn beta;
        intros iv [K|[(b & Hb & K1 & K2)|K]]; left;
        [ clear - K Q2; lia
        | pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _); clear - E5 K2 AS1 Q2; lia
        | pose proof (fs_scratch_range H HH _ _ _ RFS1 K) as [_ [_ KU]]; clear - KU AS1 Q2; lia ]
    | |- exists Xq, Forall _ Xq /\ _ =>
        destruct XA1 as (XSq & FXq & INq & XA1');
        exists (XSq ++ XS); split; [| split; [intros q Hq; apply rin_ivs_app; left; exact (INq q Hq)|]];
        [ apply Forall_app; split; [exact FXq| eapply Forall_impl; [| exact FXS]; intros iv; apply (ECH_AKit.fs_scratch_mono H)]
        | eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XA1'| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq]]|];
          eapply (xpres_of_munch_gen H); [exact MU| exact WM|]; intros a Ha [Ca HXa]; apply outside_of_not_rin; intros RW; subst W; apply rin_ivs_app in RW; destruct RW as [RW|RW];
          [ destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra); pose proof (proj1 (Forall_forall _ _) FW00 iv Hiv) as K; cbn beta in K; destruct K as [K|(b & Hb & K1 & K2)];
            [ exact ((RCI client_not_frame) _ _ _ _ _ HP SUB0 Ca ltac:(clear - K Ra Q2 LO STK0; lia))
            | pose proof (client_outside_block H HH s1' Lall m1 b LB (bv_unsigned sp) a HP1 (INX _ Hb) (fun b0 Hb0 => IN0 _ (SQ _ Hb0))
                          ltac:(intros c c' Hc Hc' E; destruct Hc as [<-|[]]; exact (D2 _ _ Hb (SQ _ Hc') E)) ltac:(clear - AS1 Q2; lia) Ca) as OB;
              clear - OB K1 K2 Ra; lia ]
          | apply HXa; apply rin_ivs_app; left; apply rin_ivs_app; right; exact RW ] ]
    | |- ?G => idtac "CWWS_LEFT" G
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cw_xs : forall Lx Lx' p A nA R' ff fp fk1 fk2 jg e5 n um uf um' uf' m1 s1' m2 s2' XS (errv2 : word),
    CW Lx p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' ->
    xpres H (Lx ++ (p, A, nA) :: L0c) S1c (memflag_foot ++ XS) m1 m2 -> Forall (fs_scratch H (LF1c ff fp)) XS -> MEMFLAG m2 1 ->
    as_RHEAP H s2' (Lx' ++ (p, A, nA) :: L0c) m2 -> (forall b, In b Lx -> In b Lx') ->
    mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c -> as_rauxv_ok H m2 B ->
    rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> as_RFS H (LF1c ff fp) m2 -> LEDGERc s2' um' uf' ->
    CW Lx' p A nA R' ff fp fk1 fk2 jg e5 n um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRL RPFLAT.
    intros until errv2. intros Wd XPm FXS MF2 HP2 LXX MI2 AC2 STK2 AUX2 ERR2 RFS2 LED2.
    pose proof Wd as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (INF : In (6, ff, fp) (LF1c ff fp)) by (left; reflexivity).
    set (Lall := Lx ++ (p, A, nA) :: L0c) in *. set (Lq := (p, A, nA) :: L0c) in *.
    assert (IN0 : forall b, In b Lq -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; exact Hb).
    assert (SQ : forall b, In b LB -> In b Lq) by (intros b Hb; subst Lq; right; exact (SUB0 _ Hb)).
    assert (BRS : forall b, In b Lall -> ablock_range H (blk_addr b) (blk_size b)) by (intros b Hb; exact (ah_blocks H HH _ _ _ _ HP1 Hb)).
    assert (MBLB : forall b, In b (blocks_MEMBIO mb R') -> In b LB).
    { intros b Hb. rewrite (mb_static_blocks mb R R' MST) in Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    pose proof LM1 as (_ & MFa & _). rewrite MF1 in MFa.
    pose proof (ECH_AC14_kit.axpres_drop_memflag H Lall S1c [] XS m1 m2 MFa MF2 ltac:(cbn [app]; exact XPm)) as XP. cbn [app] in XP.
    (* [comment removed for export] *)
    assert (SCF : forall iv, fs_scratch H (LF1c ff fp) iv -> fswin H iv).
    { intros iv [->|(k & ff' & fp' & FF & E)]; [right; left; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE; clear; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (Kk & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). pose proof (fsz_pos k ltac:(clear - Kk; lia)) as FZ.
      destruct E as [-> |[-> | ->]]; cbn [fst snd].
      - right; left. cbn [fst snd]. unfold AFS_HDR in P5. clear - P5 P6 FZ. lia.
      - right; left. cbn [fst snd]. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. clear - P3 P4. lia.
      - right; right. cbn [fst snd]. pose proof (sh_mono _ _ ltac:(clear - P5; unfold AFS_HDR in P5; assert (as_FSB H <= ff') by lia; exact H0)) as SM1. pose proof (sh_mono _ _ P6) as SM2.
        assert (E8 : sh (ff' + fsz k) = sh ff' + fshn k) by (unfold fshn, fsz, sh; clear - M8; Z.div_mod_to_equations; nia). rewrite <- E8. clear - SM1 SM2. lia. }
    assert (FW : Forall (fswin H) XS) by (eapply Forall_impl; [exact SCF| exact FXS]).
    (* [comment removed for export] *)
    assert (AVB : forall b Aq nq, In b Lq -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> avoids XS Aq nq /\ shavoids XS Aq nq).
    { intros b Aq nq Hb HA HB N0. pose proof (BRS b (IN0 _ Hb)) as BR. pose proof BR as (E1 & E2 & E3 & _). split.
      - unfold avoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_placed H HH _ _ _ _ _ Aq nq RFS1 FXS BR HA HB) Hiv).
      - unfold shavoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_placed_sh H HH _ _ _ _ _ (sh Aq) (nsh nq) RFS1 FXS BR (sh_mono _ _ HA) (sh_nsh_sub (blk_addr b) (blk_size b) Aq nq ltac:(clear - E1; lia) E2 HA HB N0)) Hiv). }
    assert (TAD : forall q Aq nq, In (q, Aq, nq) Lq -> addressable m1 Aq nq -> addressable m2 Aq nq).
    { intros q Aq nq Hb AD. pose proof (BRS _ (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5.
      eapply (addressable_xpres_blkX H Lall m1 m2 S1c XS q); [exact (IN0 _ Hb)| unfold AAPP_HI; clear - E5 ACB; lia| exact AD| exact XP|].
      exact (proj2 (AVB (q, Aq, nq) Aq nq Hb ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3)). }
    pose proof (BRS _ (IN0 _ ltac:(left; reflexivity))) as (EA1 & EA2 & EA3 & EA4 & EA5 & EA6 & EA7). cbn [blk_addr blk_size fst snd] in EA1, EA2, EA3, EA4, EA5, EA6, EA7.
    pose proof DSL as DSL1. unfold zlength in DSL1.
    assert (AVS : forall Aq nq, aceil <= Aq -> avoids XS Aq nq).
    { intros Aq nq HA. unfold avoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_hi H HH _ _ _ Aq nq RFS1 FXS HA) Hiv). }
    unfold CW. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
    | |- 1 <= mb_len R => clear - LR; lia
    | |- mb_len R <= _ => clear - LR; lia
    | |- MEMBIO H LB _ mb _ =>
        eapply (AMEMBIO_xpres H LB Lall S1c XS m1 m2); [exact MBO1| intros b Hb; exact (IN0 _ (SQ _ (MBLB _ Hb)))| exact XP|];
        apply Forall_forall; intros iv Hiv; apply Forall_forall; intros b Hb; cbn beta;
        exact (proj1 (Forall_forall _ _) (proj1 (AVB b _ _ (SQ _ (MBLB _ Hb)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b (IN0 _ (SQ _ (MBLB _ Hb)))) as (_ & _ & E3 & _); exact E3))) iv Hiv)
    | |- bytes_at asegs _ (mb_buf R) ds =>
        destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]];
        eapply (xpres_bytes_at' H); [exact XP| exact DSm1| right; right; left; exists (pD, mb_buf R, mb_len R); split; [exact (IN0 _ (SQ _ PIN))| cbn; rewrite DSL1; clear; lia]|];
        rewrite DSL1; exact (proj1 (AVB (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) (SQ _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) ltac:(clear - LR; lia)))
    | |- bytes_at asegs _ _ ds =>
        eapply (xpres_bytes_at' H); [exact XP| exact DSA1| right; right; left; exists (p, A, nA); split; [exact (IN0 _ ltac:(left; reflexivity))| cbn; rewrite DSL1; clear - LR; lia]|];
        rewrite DSL1; exact (proj1 (AVB (p, A, nA) A (mb_len R) ltac:(left; reflexivity) ltac:(apply Z.le_refl) ltac:(cbn; clear - LR; lia) ltac:(clear - LR; lia)))
    | |- exists j, rw_cells asegs _ _ [CB _ ds; CB _ j] =>
        exists junk1; eapply (xpres_rw_cells' H); [exact XP| exact JK1| right; right; left; exists (p, A, nA); split; [exact (IN0 _ ltac:(left; reflexivity))| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - LR DSL1; lia]|];
        cbn [cells_size csize Nat.add]; eapply avoids_sub; [exact (proj1 (AVB (p, A, nA) A nA ltac:(left; reflexivity) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) ltac:(clear - LR; lia)))| apply Z.le_refl| clear - LR DSL1; lia]
    | |- addressable _ st STORE_SIZE => exact (TAD (es_id S) st STORE_SIZE (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) SAD1)
    | |- addressable _ _ _ => exact (TAD p A nA ltac:(left; reflexivity) ADA1)
    | |- SLOTS _ _ _ _ _ => eapply SLOTS_carry; [| exact SL1]; intros Aq cs RC HA; eapply (xpres_rw_cells' H); [exact XP| exact RC| left; exact HA| apply AVS; clear - HA AS1; lia]
    | |- rw_cells asegs _ (S1c + 344) _ => eapply (xpres_rw_cells' H); [exact XP| exact GP1| left; clear; lia| apply AVS; clear - AS1; lia]
    | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => eapply (xpres_rw_cells' H); [exact XP| exact SV1| left; clear - Q2; lia| apply AVS; clear - AS1 Q2; lia]
    | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) =>
        pose proof FRM1 as [[WF _] _]; cbn in WF;
        eapply (xpres_rw_cells' H); [exact XP| exact FRM1| right; right; right; right; left; unfold arp_fframe; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - WF FQ5 FQ6; lia|];
        unfold arp_fframe; cbn [cells_size csize Nat.add length];
        eapply (avoids_sub XS ff 4096); [unfold avoids; apply Forall_forall; intros iv Hiv; exact (djF_inv _ _ _ _ (dj_scratch_live H HH _ _ _ 6 ff fp ff 4096 RFS1 INF FXS ltac:(apply Z.le_refl) ltac:(change (fsz 6) with 4096; apply Z.le_refl)) Hiv)| apply Z.le_refl| clear - WF; lia]
    | |- rw_cells asegs _ _ (arp_fshadow _ _ _ _ _ _ _ _ _) =>
        rewrite SHF in FSH1 |- *; pose proof FSH1 as [[WF _] _]; cbn in WF;
        pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia);
        pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL; pose proof (sh_mono (ff + 4096) _ FQ6) as SYU;
        eapply (xpres_rw_cells' H); [exact XP| exact FSH1| right; right; right; right; right; left; unfold arp_fshadow; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - WF SYL SYU SY8; lia|];
        unfold arp_fshadow; cbn [cells_size csize Nat.add length];
        eapply (avoids_sub XS (sh ff) 512); [unfold avoids; apply Forall_forall; intros iv Hiv; exact (djF_inv _ _ _ _ (dj_scratch_live_sh H HH _ _ _ 6 ff fp (sh ff) 512 RFS1 INF FXS ltac:(apply Z.le_refl) ltac:(change (fshn 6) with 512; apply Z.le_refl)) Hiv)| apply Z.le_refl| clear - WF; lia]
    | |- exists e, rw_cells asegs _ (errno_addr _) [C4 e] => exists errv2; exact ERR2
    | |- LIBMID LIB _ M =>
        eapply (LIBMID_xfs0 H HH s1' m1 LIB Lall S1c XS m1 m2 M x); [exact HP1| exact LM1| exact CTX| exact XP| intros b Hb; exact (IN0 _ (SQ _ (SUBL _ Hb)))| intros b Hb; apply IN0; subst Lq; right; unfold L0; apply in_or_app; left; exact Hb| exact FW]
    | |- rw_cells asegs _ st _ =>
        eapply (xpres_rw_cells' H); [exact XP| exact SC1| right; right; left; exists (es_id S, st, STORE_SIZE); split; [exact (IN0 _ (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)))| cbn; unfold STORE_SIZE; clear; lia]|];
        cbn [cells_size csize Nat.add]; eapply avoids_sub; [exact (proj1 (AVB (es_id S, st, STORE_SIZE) st STORE_SIZE (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(unfold STORE_SIZE; clear; lia)))| apply Z.le_refl| unfold STORE_SIZE; clear; lia]
    | |- MEMBIO_shad _ mb _ =>
        destruct MSH1 as (X1 & X2 & X3 & X4); pose proof MBO1 as MBq; destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _);
        unfold MEMBIO_shad; split; [| split; [| split]];
        [ exact (TAD _ _ _ (SQ _ J1) X1) | exact (TAD _ _ _ (SQ _ J2) X2) | exact (TAD _ _ _ (SQ _ J3) X3) | exact (TAD _ _ _ (SQ _ J4) X4) ]
    | |- accessible _ (mb_buf R) (mb_len R) =>
        destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]]; pose proof (BRS _ (IN0 _ (SQ _ PIN))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7); cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7;
        eapply (accessible_xpresX H HX s1' Lall m1 Lall m1 m2 S1c XS); [exact HP1| intros b Hb; exact Hb| exact AS1| left; exists (pD, mb_buf R, mb_len R); split; [exact (IN0 _ (SQ _ PIN))| cbn; clear; lia]| exact PAYa1| exact XP|];
        pose proof (proj2 (AVB (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) (SQ _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) E3)) as K; unfold shavoids in K;
        eapply Forall_impl; [| exact K]; cbn beta; intros iv [K1|K1]; [left| right; exact K1];
        assert (SHE : sh (mb_buf R + mb_len R - 1) + 1 <= sh (mb_buf R) + nsh (mb_len R)) by (unfold sh, nsh; clear - E2 E3; Z.div_mod_to_equations; lia); clear - K1 SHE; lia
    | |- stack0 _ lo _ => eapply (stack0_xpres H); [exact XP| exact ST01| eapply Forall_impl; [| exact FXS]; intros iv K; exact (fs_scratch_stack0_ok H HH _ _ _ RFS1 K)]
    | |- as_chain H _ _ _ =>
        eapply (chain_via_xpres_off H HH Lall S1c XS); [exact CHN1| exact XP| intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]|];
        eapply Forall_impl; [| exact FXS]; cbn beta; intros iv K; left; pose proof (fs_scratch_range H HH _ _ _ RFS1 K) as [_ [_ KU]]; exact KU
    | |- exists Xq, Forall _ Xq /\ _ =>
        destruct XA1 as (XSq & FXq & INq & XA1');
        exists (XSq ++ XS); split; [| split; [intros q Hq; apply rin_ivs_app; left; exact (INq q Hq)|]];
        [ apply Forall_app; split; [exact FXq| eapply Forall_impl; [| exact FXS]; intros iv; apply (ECH_AKit.fs_scratch_mono H)]
        | eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XA1'| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq]]|];
          intros a Ha [Ca HXa]; apply XP; [exact Ha|]; split; [eapply (aclient_addr_weaken H); [exact Ca| clear - Q2; lia| intros b Hb; exact (IN0 _ (SQ _ Hb))]|];
          intros RW; apply HXa; apply rin_ivs_app; left; apply rin_ivs_app; right; exact RW ]
    | |- ?G => idtac "CWXS_LEFT" G
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cw_rfs0 : forall sq Lall W m1 m2 LFq,
    as_RHEAP H sq Lall m1 -> as_RFS H LFq m1 -> munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b Lall /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    as_RFS H LFq m2.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRL RPFLAT.
    intros sq Lall W m1 m2 LFq HPq RF MU WM FW.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR).
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4).
    eapply (ah_RFS_frame H HH); [exact RF| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. cbn beta. intros iv [[K1 K2]|(b & Hb & K1 & K2)]; left.
    - split; right; [clear - K1 AF2 CEIL; lia| unfold ATLS_PRIV_HI, ATP; clear - K1 CEIL ACB; lia].
    - pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      split; [clear - E6 K1 K2; lia| right; unfold ATLS_PRIV_HI, ATP; unfold AIMG_TOP in E4; clear - E4 K1; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma MEMBIO_self : forall L m' a Rm, MEMBIO H L m' a Rm -> MEMBIO H (blocks_MEMBIO a Rm) m' a Rm.
  Proof.
    clear. intros L m' a Rm MB. destruct MB as (X1 & X2 & X3 & X4 & I1 & I2 & I3 & I4 & REST).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    split; [left; reflexivity|]. split; [right; left; reflexivity|]. split; [right; right; left; reflexivity|]. split; [right; right; right; left; reflexivity|]. exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma winX_blk : forall sq Lall m0 b' Aq nq iv,
    as_RHEAP H sq Lall m0 -> In b' Lall -> 0 <= Aq -> 0 <= nq -> Aq + nq <= AAPP_HI ->
    blk_addr b' <= fst iv -> snd iv <= blk_addr b' + blk_size b' -> winX Aq nq iv.
  Proof.
    clear - HH. intros sq Lall m0 b' Aq nq iv HPq Hb A0q N0 TOP K1 K2.
    pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'.
    assert (SB0 : ASHADOW_BASE <= sh Aq) by (unfold sh; clear - A0q; Z.div_mod_to_equations; lia).
    pose proof (sh_nsh_high Aq nq A0q N0 TOP) as SNH.
    unfold winX. unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' SNH SB0. rewrite ?ASHADOW_BASE_val in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma winX_stk : forall Aq nq iv, lo <= fst iv -> winX Aq nq iv.
  Proof. clear - CEIL. intros Aq nq iv K. unfold winX. right; left. pose proof aceil_range as ACR. unfold AHI_LO. clear - K CEIL ACR. lia. Qed.

  (* [comment removed for export] *)
  Lemma errblocks_bounds : forall Lq m' M', LIBMID Lq m' M' -> Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES.
  Proof.
    clear. intros Lq m' M' LMq. pose proof LMq as (_ & _ & _ & _ & EX & _ & _ & FIT & _). unfold mid_errblocks. unfold ERRX in EX.
    destruct (mid_err M') as [|c].
    - rewrite EX. rewrite blocks_ERRST_zero. cbn. unfold ERRSTR_CNT, ERRSTR_BYTES. lia.
    - apply errst_fits_bounds; [exact (proj1 (proj1 EX))| exact FIT].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rc_stack3_gen : forall xq eph,
       NEWMEMBUF_STACK (CtxReady xq) + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ BIONEW_B64_STACK xq + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ BIOPUSH_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ BIOREAD_B64_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ CMALLOC_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ BIOACC_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK)
    /\ BIOFREEALL_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack (CtxReady xq)) (errph_stack eph)) AREALLOC_STACK).
  Proof. clear. intros xq [|?]; repeat split; vm_compute; discriminate. Qed.
  Lemma rc_stack3 : NEWMEMBUF_STACK (CtxReady x) + 464 <= READCFG_STACK M /\ BIONEW_B64_STACK x + 464 <= READCFG_STACK M /\ BIOPUSH_STACK + 464 <= READCFG_STACK M
                    /\ BIOREAD_B64_STACK + 464 <= READCFG_STACK M /\ CMALLOC_STACK + 464 <= READCFG_STACK M /\ BIOACC_STACK + 464 <= READCFG_STACK M
                    /\ BIOFREEALL_STACK + 464 <= READCFG_STACK M.
  Proof. clear - CTX. unfold READCFG_STACK, mid_stack. rewrite CTX. apply rc_stack3_gen. Qed.

  (* [comment removed for export] *)
  Definition B64_UM : Z := FMT_UM + 208 + 2804 + 1500.
  Definition B64_UF : Z := FMT_UF.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma btfree_chain : forall p A nA pbin Bb nB bs R' a FBl MBl mb2 ff fp n fj24 tpb fj128 fj2 jz jg e5,
    1 <= mb_len R <= nA -> 0 <= zlength bs <= nB ->
    (DCB btfree_stmt) p A nA pbin Bb nB bs R' a (FBl ++ MBl) (chainBT H (FBl ++ MBl) a mb2 FBl MBl) ff fp n fj24 tpb fj128 fj2 jz jg e5.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRL RPFLAT.
    intros until e5. intros NARq NBRq. unfold btfree_stmt.
    intros NB S' M' LE fr1 fr3 wee v192 v200 v208 v224 v232 tpl um uf m1 s1' msF1 mo1 ra0 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 Q.
    intros DW RA0 RAE0 DNB PF0 UFB UMB VIS1 KREL1 MP1 K.
    set (TB := FBl ++ MBl) in *.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof rc_stack3 as (_ & _ & _ & _ & _ & _ & STKF).
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS1) as FRESH1.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH1) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (INF : In (6, ff, fp) (LF1c ff fp)) by (left; reflexivity).
    destruct BT1 as (R9 & d9 & M9 & BU & BLK & NX & ECX & BAP & BSH & MB & MBK & MNX & MAP & MSHc).
    set (Lall := mid_errblocks M' ++ drest LB p A nA pbin Bb nB TB [] NB LE) in *.
    pose proof (drest_sub LIB LB SUBL p A nA pbin Bb nB TB [] NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (INall : forall b, In b (drest LB p A nA pbin Bb nB TB [] NB LE) -> In b Lall) by (intros b Hb; unfold Lall; apply in_or_app; right; exact Hb).
    pose proof LM1 as (IM1' & MFq1 & CP1 & _ & _ & _ & _ & _ & GM1 & _ & _ & MM1 & MB1' & _ & RL1 & _).
    pose proof STP as (MF1' & CXS & _). rewrite MF1' in MFq1. rewrite CTX1, CTX in CP1. pose proof (eq_trans CTX1 CTX) as CTX1'.
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ HP1) as ND. unfold Lall, drest in ND. cbn [app] in ND.
    destruct (nd_app _ _ ND) as [D1 NDa]. destruct (nd_app _ _ NDa) as [D2 NDb]. destruct (nd_app _ _ NDb) as [D3 NDc].
    assert (NDT : List.NoDup (map blk_id TB)) by (rewrite map_app in NDb; exact (List.NoDup_app_remove_r _ _ NDb)).
    assert (NTB : forall b, In b (mid_errblocks M') \/ In b NB \/ In b ((pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) -> ~ In b TB).
    { intros b [Hb|[Hb|Hb]] HT.
      - exact (D1 _ _ Hb ltac:(apply in_or_app; right; apply in_or_app; left; exact HT) eq_refl).
      - exact (D2 _ _ Hb ltac:(apply in_or_app; left; exact HT) eq_refl).
      - exact (D3 _ _ HT Hb eq_refl). }
    (* [comment removed for export] *)
    pose proof BFALL as BF. unfold biofreeall_stmt in BF.
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    assert (COSTB : BIOFREEALL_COST H <= as_Cf H 4096).
    { unfold BIOFREEALL_COST, BIOFREEINT_B64_COST, B64FREE_COST, BIOFREE_COST. unfold ENCCTX_SIZE, B64CTX_SIZE, BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE.
      pose proof (CFadd 0 92 ltac:(clear; lia) ltac:(clear; lia)) as Y1. pose proof (CFadd (0 + 92) 2584 ltac:(clear; lia) ltac:(clear; lia)) as Y2.
      pose proof (CFadd (0 + 92 + 2584) 0 ltac:(clear; lia) ltac:(clear; lia)) as Y3. pose proof (CFadd (0 + 92 + 2584 + 0) 128 ltac:(clear; lia) ltac:(clear; lia)) as Y4.
      pose proof (CFadd 32 32 ltac:(clear; lia) ltac:(clear; lia)) as Y5. pose proof (CFadd (32 + 32) 16 ltac:(clear; lia) ltac:(clear; lia)) as Y6.
      pose proof (CFadd (32 + 32 + 16) 0 ltac:(clear; lia) ltac:(clear; lia)) as Y7. pose proof (CFadd (32 + 32 + 16 + 0) 128 ltac:(clear; lia) ltac:(clear; lia)) as Y8.
      pose proof (CFadd (0 + 92 + 2584 + 0 + 128) (32 + 32 + 16 + 0 + 128) ltac:(clear; lia) ltac:(clear; lia)) as Y9.
      pose proof (CFmono (0 + 92 + 2584 + 0 + 128 + (32 + 32 + 16 + 0 + 128)) 4096 ltac:(clear; lia)) as Y10.
      clear - Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10. lia. }
    eapply (ah_seq H HH).
    { eapply BF with (x := x) (a := a) (mb := mb2) (lo := lo) (B := B) (R := R9) (M := M9) (d := d9) (errv := errv1) (LB := Lall) (LF := LF1c ff fp) (CH := CH1c); clear BF.
      all: try first [exact VIS1| exact HP1| exact KREL1| exact AUX1| exact MI1| exact IM1'| exact GM1| exact MFq1| exact MM1| exact MB1'| exact RL1| exact CEIL| exact AC1| exact CHN1| exact RFS1| exact ERR1| exact BAP| exact NX| exact MNX| exact MAP| exact BSH| exact MSHc| exact CHBx].
      all: lazymatch goal with
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- B64F_used _ _ _ _ _ => eapply B64F_used_rebase; [exact BU| rewrite BLK; intros b Hb; apply INall; apply STB; unfold TB; apply in_or_app; left; exact Hb]
           | |- ENCCTX _ _ _ _ _ _ => eapply ENCCTX_rebase; [exact ECX| apply INall; apply STB; pose proof BU as (_ & _ & (_ & _ & I3 & _)); exact I3]
           | |- MEMBIO _ _ _ _ _ => eapply (MEMBIO_mono H); [exact MB| intros b Hb; apply INall; apply STB; exact Hb]
           | |- CTXPH _ _ _ => eapply (CTXPH_mono (LE ++ LIB)); [intros b Hb; apply INall; apply SLL; exact Hb| exact CP1]
           | |- List.NoDup _ => rewrite BLK, MBK; exact NDT
           | |- stack0 _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); eapply stack0_sub; [exact STK1| apply Z.le_refl| clear - Q2 CEIL LO STK0; lia| clear - Q1; Z.div_mod_to_equations; lia]
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST1
           | |- lo <= _ - _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- (length _ < _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; clear - LFB; lia
           | |- pf_ok _ _ _ _ => rewrite unsigned_lit by (clear - RA0; lia); rewrite <- PF9FREE; exact PF0
           | |- BIOFREEALL_COST _ <= _ => destruct LED1 as (L0' & L1' & L2');
                 pose proof ((RCI LEDGER_pay) s1' um uf 0 4096 (conj L0' (conj L1' L2')) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - UMB; lia) ltac:(clear - UFB; lia)) as PY;
                 pose proof (CM0 0 ltac:(clear; lia)) as Y0; clear - PY Y0 COSTB; lia
           | |- bv_unsigned _ mod 2 = 0 => rewrite unsigned_lit by (clear - RA0; lia); exact RAE0
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHBx _ _ Hin)
           | |- ?G => idtac "BFALL_LEFT" G
           end. }
    clear BF. intros [msF2 mo2] PO. unfold biofreeall_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & errv2 & s2' & LBr & XS2 & VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2
                    & HP2 & PERM2 & MF2 & IM2 & GM2 & MB2' & MM2 & RL2 & CP2 & STK2 & FXS2 & RFS2 & XP2 & AL2).
    rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    rewrite BLK, MBK, app_assoc in PERM2. fold TB in PERM2.
    (* [comment removed for export] *)
    assert (KEEP : forall b, In b (mid_errblocks M') \/ In b NB \/ In b ((pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) -> In b LBr).
    { intros b Hb. eapply perm_in_rest_s; [apply Permutation_sym; exact PERM2| | exact (NTB b Hb)].
      unfold Lall, drest. cbn [app]. destruct Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
    assert (KLB : forall b, In b LB -> In b LBr) by (intros b Hb; apply KEEP; right; right; right; right; apply in_or_app; right; exact Hb).
    assert (KLE : forall b, In b LE -> In b LBr) by (intros b Hb; apply KEEP; right; right; right; right; apply in_or_app; left; exact Hb).
    assert (KNB : forall b, In b NB -> In b LBr) by (intros b Hb; apply KEEP; right; left; exact Hb).
    assert (KE : forall b, In b (mid_errblocks M') -> In b LBr) by (intros b Hb; apply KEEP; left; exact Hb).
    assert (KPB : In (pbin, Bb, nB) LBr) by (apply KEEP; right; right; left; reflexivity).
    assert (KPA : In (p, A, nA) LBr) by (apply KEEP; right; right; right; left; reflexivity).
    assert (PT : Permutation LBr (mid_errblocks M' ++ NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { apply (Permutation_app_inv_l TB). transitivity Lall; [apply Permutation_sym; exact PERM2|]. unfold Lall, drest. cbn [app].
      rewrite !(app_assoc (mid_errblocks M') NB). apply (Permutation_app_swap_app (mid_errblocks M' ++ NB) TB). }
    assert (HP2' : as_RHEAP H s2' (mid_errblocks M' ++ NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) m2) by (eapply PERM; [exact HP2| exact PT]).
    (* [comment removed for export] *)
    assert (XP2' : xpres H LBr S1c XS2 m1 m2).
    { eapply xpres_drop_same14; [exact XP2|]. intros q Hq. unfold mutex_foot in Hq. cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
      destruct CP1 as [_ [EX1 _]]. destruct CP2 as [_ [EX2 _]]. destruct EX1 as (I5 & Z5 & _ & MU1). destruct EX2 as (_ & _ & _ & MU2).
      pose proof (ah_blocks H HH _ _ _ _ HP1 (INall _ (SLL _ I5))) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). rewrite Z5 in P5. unfold MUTEX_SIZE in P5. unfold AIMG_TOP in P4.
      eapply (rw_cells_same_raw_hi14 m1 m2 _ _ q MU1 MU2); [unfold AIMG_TOP; exact P4| cbn; clear - P5 ACB; lia| cbn; clear - Hq; lia]. }
    (* [comment removed for export] *)
    assert (BRS : forall b, In b LBr -> ablock_range H (blk_addr b) (blk_size b)) by (intros b Hb; exact (ah_blocks H HH _ _ _ _ HP2 Hb)).
    assert (AVB : forall b Aq nq, In b LBr -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> avoids XS2 Aq nq /\ shavoids XS2 Aq nq).
    { intros b Aq nq Hb HA HB N0. pose proof (BRS b Hb) as BR. pose proof BR as (E1 & E2 & E3 & _). split.
      - unfold avoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_placed H HH _ _ _ _ _ Aq nq RFS1 FXS2 BR HA HB) Hiv).
      - unfold shavoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_placed_sh H HH _ _ _ _ _ (sh Aq) (nsh nq) RFS1 FXS2 BR (sh_mono _ _ HA) (sh_nsh_sub (blk_addr b) (blk_size b) Aq nq ltac:(clear - E1; lia) E2 HA HB N0)) Hiv). }
    assert (AVS : forall Aq nq, aceil <= Aq -> avoids XS2 Aq nq).
    { intros Aq nq HA. unfold avoids. apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ (dj_scratch_hi H HH _ _ _ Aq nq RFS1 FXS2 HA) Hiv). }
    assert (TAD : forall q Aq nq, In (q, Aq, nq) LBr -> addressable m1 Aq nq -> addressable m2 Aq nq).
    { intros q Aq nq Hb AD. pose proof (BRS _ Hb) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5.
      eapply (addressable_xpres_blkX H LBr m1 m2 S1c XS2 q); [exact Hb| unfold AAPP_HI; clear - E5 ACB; lia| exact AD| exact XP2'|].
      exact (proj2 (AVB (q, Aq, nq) Aq nq Hb ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3)). }
    assert (TRC : forall b Aq cs, In b LBr -> blk_addr b <= Aq -> Aq + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs m1 Aq cs -> rw_cells asegs m2 Aq cs).
    { intros b Aq cs Hb HA HB RC. eapply (xpres_rw_cells' H); [exact XP2'| exact RC| right; right; left; exists b; split; [exact Hb| split; [exact HA| exact HB]]|].
      exact (proj1 (AVB b Aq _ Hb HA HB ltac:(clear; lia))). }
    assert (TRS : forall Aq cs, rw_cells asegs m1 Aq cs -> S1c <= Aq -> rw_cells asegs m2 Aq cs).
    { intros Aq cs RC HA. eapply (xpres_rw_cells' H); [exact XP2'| exact RC| left; exact HA| apply AVS; clear - HA AS1; lia]. }
    pose proof (BRS _ KPB) as (Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6 & Pb7). cbn [blk_addr blk_size fst snd] in Pb1, Pb2, Pb3, Pb4, Pb5, Pb6, Pb7.
    pose proof (BRS _ KPA) as (Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6 & Pa7). cbn [blk_addr blk_size fst snd] in Pa1, Pa2, Pa3, Pa4, Pa5, Pa6, Pa7.
    pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof CBb1 as [[WFb _] _]. cbn in WFb. destruct WFb as (LB1 & LJ1 & _).
    pose proof CBa1 as [[WFa _] _]. cbn in WFa. destruct WFa as (LA1 & LJA1 & _).
    (* [comment removed for export] *)
    destruct XA1 as (XSq & FXq & INq & XA1').
    eapply (K m2 s2' msF2 mo2 errv2 (uf + 4096) (XSq ++ XS2) w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 VIS2 KREL2 (ah_mpres_trans H HH _ _ _ MP1 MP2) HP2' MI2 AC2 ST2).
    all: lazymatch goal with
    | |- stack0 _ lo _ => eapply (stack0_xpres H); [exact XP2'| exact STK1| eapply Forall_impl; [| exact FXS2]; intros iv Kq; exact (fs_scratch_stack0_ok H HH _ _ _ RFS1 Kq)]
    | |- rw_cells asegs _ (errno_addr _) _ => exact ERR2
    | |- as_rauxv_ok _ _ _ => exact AUX2
    | |- as_RFS _ _ _ => exact RFS2
    | |- LIBMID _ _ _ => eapply (LIBMID_xs H HH s2' m2 (LE ++ LIB) LBr S1c XS2 (LF1c ff fp) m1 m2 M' x);
                          [exact HP2| exact RFS1| exact FXS2| exact LM1| exact CTX1'| exact XP2'| intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (KLE _ Hb)| exact (KLB _ (SUBL _ Hb))]| exact KE]
    | |- STOREobj _ _ _ _ => eapply (STOREobj_frameX H (NB ++ LE ++ LB) S1c XS2 m1 m2); [exact SO1| |];
                              [ eapply (xpres_weaken H); [exact XP2'| apply Z.le_refl| intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (KNB _ Hb)| apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (KLE _ Hb)| exact (KLB _ Hb)]]| intros q Hq; exact Hq]
                              | intros b Hb; pose proof (Permutation_in _ SPM Hb) as Hb'; assert (HbL : In b LBr) by (destruct Hb' as [<-|Hb']; [apply KLB; exact (proj1 (proj2 SO))| exact (KNB _ Hb')]);
                                exact (proj1 (AVB b _ _ HbL ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b HbL) as (_ & _ & E3 & _); exact E3))) ]
    | |- STORE_shad _ _ _ => eapply (STORE_shad_frameX H (NB ++ LE ++ LB) LBr S1c XS2 m1 m2); [exact SSH1| exact SO1| exact XP2'|];
                             intros b Hb; pose proof (Permutation_in _ SPM Hb) as Hb'; assert (HbL : In b LBr) by (destruct Hb' as [<-|Hb']; [apply KLB; exact (proj1 (proj2 SO))| exact (KNB _ Hb')]);
                             split; [exact HbL| exact (AVB b _ _ HbL ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b HbL) as (_ & _ & E3 & _); exact E3))]
    | |- MEMBIO _ LB _ mb _ =>
        assert (MBLB : forall b, In b (blocks_MEMBIO mb R') -> In b LB) by (intros b Hb; destruct MBO1 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption);
        eapply (AMEMBIO_xpres H LB LBr S1c XS2 m1 m2); [exact MBO1| intros b Hb; exact (KLB _ (MBLB _ Hb))| exact XP2'|];
        apply Forall_forall; intros iv Hiv; apply Forall_forall; intros b Hb; cbn beta;
        exact (proj1 (Forall_forall _ _) (proj1 (AVB b _ _ (KLB _ (MBLB _ Hb)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b (KLB _ (MBLB _ Hb))) as (_ & _ & E3 & _); exact E3))) iv Hiv)
    | |- MEMBIO_shad _ mb _ =>
        destruct MSH1 as (X1 & X2 & X3 & X4); pose proof MBO1 as MBq; destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _);
        unfold MEMBIO_shad; split; [| split; [| split]];
        [ exact (TAD _ _ _ (KLB _ J1) X1) | exact (TAD _ _ _ (KLB _ J2) X2) | exact (TAD _ _ _ (KLB _ J3) X3) | exact (TAD _ _ _ (KLB _ J4) X4) ]
    | |- bytes_at asegs _ (mb_buf R) ds =>
        destruct (PAYL ltac:(clear - NARq; lia)) as [pD [PIN _]];
        eapply (xpres_bytes_at' H); [exact XP2'| exact DSm1| right; right; left; exists (pD, mb_buf R, mb_len R); split; [exact (KLB _ PIN)| cbn; rewrite DSL1; clear; lia]|];
        rewrite DSL1; exact (proj1 (AVB (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) (KLB _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) ltac:(clear - NARq; lia)))
    | |- exists lb : byte, rw_cells asegs _ _ _ =>
        destruct FF1 as [lb0 FF1x]; exists lb0;
        pose proof FF1x as [[WF _] _]; cbn in WF;
        eapply (xpres_rw_cells' H); [exact XP2'| exact FF1x| right; right; right; right; left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - FQ5 FQ6; lia|];
        unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length];
        eapply (avoids_sub XS2 ff 4096); [unfold avoids; apply Forall_forall; intros iv Hiv; exact (djF_inv _ _ _ _ (dj_scratch_live H HH _ _ _ 6 ff fp ff 4096 RFS1 INF FXS2 ltac:(apply Z.le_refl) ltac:(change (fsz 6) with 4096; apply Z.le_refl)) Hiv)| apply Z.le_refl| clear; lia]
    | |- exists j, rw_cells asegs _ _ [CB _ ds; _] => exists ja1; eapply (TRC (p, A, nA)); [exact KPA| cbn; apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NARq LA1 LJA1 DSL1; lia| exact CBa1]
    | |- exists j, rw_cells asegs _ _ _ => exists jb1; eapply (TRC (pbin, Bb, nB)); [exact KPB| cbn; apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NBRq LB1 LJ1; unfold zlength in NBRq; lia| exact CBb1]
    | |- addressable _ _ _ => first [exact (TAD _ _ _ KPB ADb1)| exact (TAD _ _ _ KPA ADa1)]
    | |- rw_cells asegs _ S1c _ => exact (TRS _ _ FR0 ltac:(apply Z.le_refl))
    | |- rw_cells asegs _ (S1c + _) _ => first [exact (TRS _ _ FR1 ltac:(clear; lia))| exact (TRS _ _ FR2 ltac:(clear; lia))| exact (TRS _ _ FR3 ltac:(clear; lia))| exact (TRS _ _ FRG ltac:(clear; lia))]
    | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (TRS _ _ FRS ltac:(clear - Q2; lia))
    | |- rw_cells asegs _ (Z.shiftr _ 3 + ASHB) _ =>
        rewrite SHF in FSH1 |- *;
        pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia);
        pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL; pose proof (sh_mono (ff + 4096) _ FQ6) as SYU;
        eapply (xpres_rw_cells' H); [exact XP2'| exact FSH1| right; right; right; right; right; left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - SYL SYU SY8; lia|];
        unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length];
        eapply (avoids_sub XS2 (sh ff) 512); [unfold avoids; apply Forall_forall; intros iv Hiv; exact (djF_inv _ _ _ _ (dj_scratch_live_sh H HH _ _ _ 6 ff fp (sh ff) 512 RFS1 INF FXS2 ltac:(apply Z.le_refl) ltac:(change (fshn 6) with 512; apply Z.le_refl)) Hiv)| apply Z.le_refl| clear; lia]
    | |- as_chain _ _ _ _ =>
        eapply (chain_via_xpres_off H HH LBr S1c XS2); [exact CHN1| exact XP2'| exact CHBx|];
        eapply Forall_impl; [| exact FXS2]; cbn beta; intros iv Kq; left; pose proof (fs_scratch_range H HH _ _ _ RFS1 Kq) as [_ [_ KU]]; exact KU
    | |- Forall (fs_scratch H LF) _ => apply Forall_app; split; [exact FXq| eapply Forall_impl; [| exact FXS2]; intros iv; apply (ECH_AKit.fs_scratch_mono H)]
    | |- forall q, rin_ivs _ q -> rin_ivs _ q => intros q Hq; apply rin_ivs_app; left; exact (INq q Hq)
    | |- xpres _ LB _ _ m _ =>
        eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XA1'| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq]]|];
        intros a' Ha [Ca HXa]; apply XP2'; [exact Ha|]; split; [eapply (aclient_addr_weaken H); [exact Ca| clear - Q2; lia| intros b Hb; exact (KLB _ Hb)]|];
        intros RW; apply HXa; apply rin_ivs_app; left; apply rin_ivs_app; right; exact RW
    | |- LEDGERc _ _ _ => pose proof ((RCI LEDGER_step) s1' s2' um uf 0 4096 LED1 ltac:(clear; lia) ltac:(clear; lia)) as LS; rewrite Z.add_0_r in LS; apply LS; clear LS;
                          pose proof (CM0 0 ltac:(clear; lia)) as Y0; clear - AL2 COSTB Y0; lia
    | |- _ <= _ + 4096 => apply Z.le_refl
    | |- ?G => idtac "BTFREE_LEFT" G
    end.
  Qed.
  (* [comment removed for export] *)
  Lemma rp_b64arm : rp_b64Kc.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRL RPFLAT.
    unfold rp_b64K. intros p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' msF1 mo1 k rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s2w s4w s8w s9w s11w u3 u4 u5 u6.
    intros KR NEQ NR NAE L5 FW UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof rc_stack3 as (STKN & STKB & STKP & STKR & STKM & STKA & STKF).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (cw_of_afw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW) as W1.
    pose proof W1 as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(left; reflexivity)) as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). cbn [blk_addr blk_size fst snd] in BA1, BA2, BA3, BA4, BA5, BA6, BA7.
    pose proof LM1 as (IM1 & MFq1 & CP1 & _ & _ & _ & _ & _ & GM1 & _ & _ & MM1 & MB1 & _ & RL1 & _). rewrite MF1 in MFq1. rewrite CTX in CP1.
    pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    (* [comment removed for export] *)
    destruct (SLOTS_join _ _ _ _ _ SL1) as (jq1 & y16 & y24 & y32 & y40 & y48 & y56 & y64 & y72 & y80 & y88 & y192 & y200 & y208 & y224 & y232 & y240 & y248 & y256 & y264 & y272 & y280 & y288 & y296 & y304 & y312 & y320 & y328 & y336 & _ & P2a).
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply afb_seg1 with (n := n) (K := 512 * k) (q := S1c); [clear - KR; lia| exact NR| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2a| exact MI1]|].
    clear jq1 y16 y24 y32 y40 y48 y56 y64 y72 y80 y88 y192 y200 y208 y224 y232 y240 y248 y256 y264 y272 y280 y288 y296 y304 y312 y320 y328 y336 P2a.
    intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2. try unfold wz in VIS2. replace (n + 512 * k) with (mb_len R) in VIS2 by (clear - NEQ; lia).
    pose proof NEWMB as NM. unfold newmembuf_stmt in NM.
    eapply (ah_seq H HH).
    { eapply NM with (ph := CtxReady x) (LB := [] ++ (p, A, nA) :: L0c) (buf := A) (len := mb_len R) (lo := lo) (B := B) (s := s1') (errv := errv1) (LF := LF1c ff fp) (CH := CH1c); clear NM.
      all: try first [exact VIS2| exact HP1| exact KREL2| exact AUX1| exact MI1| exact IM1| exact GM1| exact MFq1| exact MM1| exact RL1| exact CEIL| exact AC1| exact CHN1| exact RFS1| exact ERR1].
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
           | |- 0 < _ => exact BA1
           | |- _ + mb_len R <= aceil => clear - BA5 LR; lia
           | |- 0 <= mb_len R < _ => clear - LT L5; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in LT; lia
           | |- lb_bytes _ + ctxph_bytes _ + MEMBIO_BYTES <= _ => cbn [app ctxph_bytes]; rewrite lb_bytes_cons; cbn [blk_size snd]; pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq; unfold DECODE_BYTES, ERRSTR_BYTES, MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *; unfold L0; clear - BUDq NAR EBR; lia
           | |- Z.of_nat (length _) + ctxph_cnt _ + 4 <= _ => cbn [app ctxph_cnt length]; pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq; unfold L0; clear - BUDq ECR; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK1
           | |- lo <= _ - _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKN Q2; lia
           | |- ctxph_sh0 _ _ _ _ => exact I
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- CTXPH _ _ _ => eapply (CTXPH_mono LIB); [intros b Hb; right; exact (SUB0 _ (SUBL _ Hb))| exact CP1]
           | |- (length _ + ctxph_frames _ <= _)%nat => unfold LF1; cbn [length ctxph_frames]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; clear - LFB; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
           | |- pf_ok _ _ _ _ => unfold AFB_R1; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; rewrite CTX; do 10 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- ctxph_closed_ok _ _ => exact I
           | |- NEWMEMBUF_COST _ _ <= _ => unfold NEWMEMBUF_COST; cbn [ctxph_cost]; destruct LED1 as (L0' & L1' & L2');
                 pose proof ((RCI LEDGER_pay) s1' um uf 208 0 (conj L0' (conj L1' L2')) ltac:(clear; lia) ltac:(clear; lia) ltac:(unfold FMT_UM, lad_cm, DECODE_CUM_BYTES in *; clear - UMB; lia) ltac:(unfold FMT_UF, lad_cf, DECODE_CUM_BYTES in *; clear - UFB; lia)) as PY;
                 pose proof (CMadd 128 16 ltac:(clear; lia) ltac:(clear; lia)) as Y1; pose proof (CMadd 144 32 ltac:(clear; lia) ltac:(clear; lia)) as Y2; pose proof (CMadd 176 32 ltac:(clear; lia) ltac:(clear; lia)) as Y3;
                 change (128 + 16) with 144 in Y1; change (144 + 32) with 176 in Y2; change (176 + 32) with 208 in Y3;
                 unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; clear - PY Y1 Y2 Y3; lia
           | |- bv_unsigned _ mod 2 = 0 => reflexivity
           | |- ?G => idtac "NEWMB_LEFT" G
           end. }
    clear NM. intros [msF3 mo3] PO. unfold newmembuf_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & s2' & LBN & LB2 & x2 & mb2 & M2 & XS2
                    & VIS3 & PM2 & MP3 & (KREL3 & MI2 & AC2 & ST2 & ERR2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & MM2 & CD2 & ADN2 & CP2 & _ & MBO2 & MBUF & MLEN & MPOS & MNRD & MNX & MPV & APOS & MAP2 & MSH2 & FXS2 & RFS2 & XP2 & AL2).
    cbn [ctxph_delta] in CD2. destruct CD2 as [-> ->]. cbn [app] in PM2, XP2.
    rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    set (MBL := blocks_MEMBIO mb2 M2) in *.
    assert (HP2' : as_RHEAP H s2' (MBL ++ (p, A, nA) :: L0c) m2) by (eapply PERM; [exact HP2| exact PM2]).
    assert (W2 : CW MBL p A nA R' ff fp fk1 fk2 jg e5 n (um + 208) uf m2 s2').
    { eapply (cw_xs [] MBL); [exact W1| cbn [app]; unfold ctxph_foot in XP2; cbn [app] in XP2; exact XP2| exact FXS2| exact MF2| exact HP2'| intros b []| exact MI2| exact AC2| exact ST2| exact AUX2| exact ERR2| exact RFS2|].
      pose proof ((RCI LEDGER_step) s1' s2' um uf 208 0 LED1 ltac:(clear; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS. clear LS.
      unfold NEWMEMBUF_COST in AL2. cbn [ctxph_cost] in AL2. revert AL2. pose proof (CMadd 128 16 ltac:(clear; lia) ltac:(clear; lia)) as Y1. pose proof (CMadd 144 32 ltac:(clear; lia) ltac:(clear; lia)) as Y2. pose proof (CMadd 176 32 ltac:(clear; lia) ltac:(clear; lia)) as Y3.
        change (128 + 16) with 144 in Y1. change (144 + 32) with 176 in Y2. change (176 + 32) with 208 in Y3.
        unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. clear - Y1 Y2 Y3. intros AL2. lia. }
    pose proof (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3)) as MPc3. clear MP2 MP3.
    pose proof (ah_blocks H HH _ _ _ _ HP2' ltac:(apply in_or_app; left; unfold MBL, blocks_MEMBIO; left; reflexivity)) as (Mb1 & Mb2 & Mb3 & Mb4 & Mb5 & Mb6 & Mb7).
    cbn [blk_addr blk_size fst snd] in Mb1, Mb2, Mb3, Mb4, Mb5, Mb6, Mb7. unfold BIO_SIZE in Mb5.
    pose proof (MEMBIO_self _ _ _ _ MBO2) as MBq2. fold MBL in MBq2.
    clear W1 HP1 MBO1 DSm1 DSA1 JK1 ADA1 SL1 GP1 SV1 FRM1 FSH1 RFS1 ERR1 AUX1 LM1 SC1 SAD1 MSH1 PAYa1 MI1 AC1 STK1 ST01 CHN1 XA1 LED1 VIS1 VIS2 KREL1 KREL2 IM1 MFq1 CP1 GM1 MM1 MB1 RL1 XP2 PM2 MBO2.
    pose proof W2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS2' & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply afb_seg2; [clear - APOS Mb5 ACB; lia| exact MI2]|].
    intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply abiofb64_spec with (lo := lo);
      [exact AC2| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST2| exact CEIL| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKA Q2; lia| exact MI2| reflexivity]|].
    cbv beta. intros msF5 mo5 KREL5 MP5 (w0' & w1' & w2' & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3' & w4' & w5' & w6' & m4 & VIS5 & MU4 & WM4 & MI4 & AC4 & ST4).
    rewrite (unsigned_lit S1c) in MU4, ST4 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (W4 : CW MBL p A nA R' ff fp fk1 fk2 jg e5 n (um + 208) uf m4 s2').
    { eapply (cw_ws MBL p A nA R' ff fp fk1 fk2 jg e5 n (um + 208) uf m2 s2' m4 [(lo, S1c)] []);
        [exact W2| rewrite app_nil_r; exact MU4| exact WM4| exact MI4| exact AC4| exact ST4| | apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl| apply Forall_nil]| apply Forall_nil].
      eapply (cw_rfs0 s2' (MBL ++ (p, A, nA) :: L0c) [(lo, S1c)] m2 m4); [exact HP2'| exact RFS2'| exact MU4| exact WM4| apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl| apply Forall_nil]]. }
    assert (MBq4 : MEMBIO H MBL m4 mb2 M2).
    { eapply (AMEMBIO_munch H MBL [(lo, S1c)] m2 m4); [exact MBq2| exact MU4| exact WM4|].
      apply Forall_cons; [| apply Forall_nil]. apply Forall_forall. intros b Hb. cbn [fst snd]. left.
      pose proof (ah_blocks H HH _ _ _ _ HP2' ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & E5 & _). clear - E5 CEIL. lia. }
    assert (MSHb4 : MEMBIO_shad m4 mb2 M2).
    { destruct MSH2 as (T1 & T2 & T3 & T4). pose proof MBq2 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & (G1 & _ & Gn1 & _ & G5 & _) & (H1' & _ & Hn1 & _ & H5 & _) & (I1' & _ & In1 & _ & I5 & _) & (K1' & _ & Kn1 & _ & K5 & _) & _).
      split; [| split; [| split]]; (eapply addressable_acrossX; [eassumption| exact MU4| exact WM4| | | apply Forall_cons; [apply winX_stk; cbn [fst]; apply Z.le_refl| apply Forall_nil]]);
        unfold AAPP_HI; clear - G1 G5 H1' H5 I1' I5 K1' K5 ACB; try lia. }
    pose proof (ah_mpres_trans H HH _ _ _ MPc3 (ah_mpres_trans H HH _ _ _ MP4 MP5)) as MPc5. clear MPc3 MP4 MP5 MU4 WM4 KREL3 KREL4 VIS3 VIS4 MI2 AC2 ST2 ERR2 AUX2 W2 HP2 HP2' RFS2' MBq2 MSH2 MF2 IM2 GM2 RL2 MM2 CP2.
    (* [comment removed for export] *)
    pose proof W4 as (HP4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS4 & [errv4 ERR4] & AUX4 & LM4 & _ & _ & _ & _ & MI4' & AC4' & STK4 & ST04 & CHN4 & XA4 & LED4).
    pose proof LM4 as (IM4 & MFq4 & CP4 & _ & _ & _ & _ & _ & GM4 & _ & _ & MM4 & MB4 & _ & RL4 & _). rewrite MF1 in MFq4. rewrite CTX in CP4.
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply afb_seg3; exact MI4|]. intros msF6 mo6 KREL6 MP6 VIS6. cbn beta in VIS6.
    pose proof BNEW as BN. unfold bionew_b64_stmt in BN.
    eapply (ah_seq H HH).
    { eapply BN with (x := x) (v := 1) (lo := lo) (B := B) (s := s2') (errv := errv4) (LB := MBL ++ (p, A, nA) :: L0c) (LF := LF1c ff fp) (CH := CH1c); clear BN.
      all: try first [exact VIS6| exact HP4| exact KREL6| exact AUX4| exact MI4| exact IM4| exact GM4| exact MFq4| exact MB4| exact RL4| exact CEIL| exact AC4| exact CHN4| exact RFS4| exact ERR4].
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
           | |- lb_bytes _ + B64F_BYTES <= _ => rewrite lb_bytes_app, lb_bytes_cons; cbn [blk_size snd]; unfold MBL; rewrite (proj1 (membio_blocks_facts mb2 M2));
                 pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq; unfold DECODE_BYTES, ERRSTR_BYTES, MEMBIO_BYTES, B64F_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, B64CTX_SIZE in *; unfold L0; clear - BUDq NAR EBR; lia
           | |- Z.of_nat (length _) + 3 <= _ => rewrite length_app; cbn [length]; unfold MBL, blocks_MEMBIO; cbn [length Nat.add]; pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq; unfold L0; clear - BUDq ECR; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK4
           | |- lo <= _ - _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKB Q2; lia
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- CTXPH _ _ _ => eapply (CTXPH_mono LIB); [intros b Hb; apply in_or_app; right; right; exact (SUB0 _ (SUBL _ Hb))| exact CP4]
           | |- (length _ + 1 <= _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; clear - LFB; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
           | |- pf_ok _ _ _ _ => unfold AFB_R3; rewrite unsigned_lit by (clear; lia); rewrite <- (PF9NEW x); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; rewrite CTX; do 11 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- BIONEW_B64_COST _ _ <= _ => unfold BIONEW_B64_COST; cbn [ctxph_cost]; destruct LED4 as (L0' & L1' & L2');
                 pose proof ((RCI LEDGER_pay) s2' (um + 208) uf 2804 0 (conj L0' (conj L1' L2')) ltac:(clear; lia) ltac:(clear; lia) ltac:(unfold FMT_UM, lad_cm, DECODE_CUM_BYTES in *; clear - UMB; lia) ltac:(unfold FMT_UF, lad_cf, DECODE_CUM_BYTES in *; clear - UFB; lia)) as PY;
                 pose proof (CMadd 128 2584 ltac:(clear; lia) ltac:(clear; lia)) as Y1; pose proof (CMadd 2712 92 ltac:(clear; lia) ltac:(clear; lia)) as Y2;
                 change (128 + 2584) with 2712 in Y1; change (2712 + 92) with 2804 in Y2; pose proof (CF0 0 ltac:(clear; lia)) as Y3; pose proof (CFmono 0 0 ltac:(clear; lia)) as Y4;
                 unfold BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE; clear - PY Y1 Y2 Y3 Y4 CF0; pose proof (CF0 0 ltac:(clear; lia)); lia
           | |- bv_unsigned _ mod 2 = 0 => reflexivity
           | |- ?G => idtac "BNEW_LEFT" G
           end. }
    clear BN. intros [msF7 mo7] PO. unfold bionew_b64_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m5 & errv5 & s5' & a & Rf & XS5 & VIS7 & KREL7 & MP7 & MI5 & AC5 & ST5 & ERR5 & AUX5
                    & HP5 & CP5 & BC5 & FL0 & RT0 & NR0 & NX0 & PV0 & [cj [CJL CJ5]] & BB5 & BAP & EC5 & APOS5 & BSH5 & MF5 & IM5 & GM5 & MB5 & RL5 & FXS5 & RFS5 & XP5 & AL5).
    cbv zeta in HP5. cbv zeta in CP5. cbv zeta in BB5. cbv zeta in EC5.
    rewrite (unsigned_lit S1c) in ST5, XP5 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    set (FB := blocks_B64F a Rf) in *.
    assert (HP5' : as_RHEAP H s5' ((FB ++ MBL) ++ (p, A, nA) :: L0c) m5) by (rewrite <- app_assoc; exact HP5).
    set (TB := FB ++ MBL) in *.
    assert (W5 : CW TB p A nA R' ff fp fk1 fk2 jg e5 n (um + 208 + 2804) uf m5 s5').
    { eapply (cw_xs MBL TB); [exact W4| exact XP5| exact FXS5| exact MF5| exact HP5'| intros b Hb; unfold TB; apply in_or_app; right; exact Hb| exact MI5| exact AC5| exact ST5| exact AUX5| exact ERR5| exact RFS5|].
      pose proof ((RCI LEDGER_step) s2' s5' (um + 208) uf 2804 0 LED4 ltac:(clear; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS. clear LS.
      unfold BIONEW_B64_COST in AL5. cbn [ctxph_cost] in AL5. revert AL5.
      pose proof (CMadd 128 2584 ltac:(clear; lia) ltac:(clear; lia)) as Y1. pose proof (CMadd 2712 92 ltac:(clear; lia) ltac:(clear; lia)) as Y2.
      change (128 + 2584) with 2712 in Y1. change (2712 + 92) with 2804 in Y2. pose proof (CF0 0 ltac:(clear; lia)) as Y3. pose proof (CFmono 0 0 ltac:(clear; lia)) as Y4.
      unfold BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE. clear - Y1 Y2 Y3 Y4. intros AL5. lia. }
    (* [comment removed for export] *)
    assert (MBq5 : MEMBIO H MBL m5 mb2 M2).
    { eapply (AMEMBIO_xpres H MBL (MBL ++ (p, A, nA) :: L0c) S1c (memflag_foot ++ XS5) m4 m5); [exact MBq4| intros b Hb; apply in_or_app; left; exact Hb| exact XP5|].
      apply Forall_app. split.
      - unfold memflag_foot. apply Forall_cons; [| apply Forall_nil]. apply Forall_forall. intros b Hb. cbn [fst snd].
        pose proof (ah_blocks H HH _ _ _ _ HP4 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & E4 & _). right. unfold A_mem_inited. unfold AIMG_TOP in E4. clear - E4. lia.
      - apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb.
        exact (djF_inv _ _ _ _ (dj_scratch_placed H HH _ _ _ _ _ (blk_addr b) (blk_size b) RFS4 FXS5 (ah_blocks H HH _ _ _ _ HP4 ltac:(apply in_or_app; left; exact Hb)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl)) Hiv). }
    assert (MSHb5 : MEMBIO_shad m5 mb2 M2).
    { destruct MSHb4 as (T1 & T2 & T3 & T4). pose proof MBq4 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & (G1 & _ & Gn1 & _ & G5 & _) & (H1' & _ & Hn1 & _ & H5 & _) & (I1' & _ & In1 & _ & I5 & _) & (K1' & _ & Kn1 & _ & K5 & _) & _).
      pose proof (ECH_AC14_kit.axpres_drop_memflag H (MBL ++ (p, A, nA) :: L0c) S1c [] XS5 m4 m5 MFq4 MF5 ltac:(cbn [app]; exact XP5)) as XP5n. cbn [app] in XP5n.
      assert (SHV : forall q Aq nq, In (q, Aq, nq) MBL -> addressable m4 Aq nq -> Aq + nq <= AAPP_HI -> addressable m5 Aq nq).
      { intros q Aq nq Hb AD TOP. eapply (addressable_xpres_blkX H (MBL ++ (p, A, nA) :: L0c) m4 m5 S1c XS5 q); [apply in_or_app; left; exact Hb| exact TOP| exact AD| exact XP5n|].
        pose proof (ah_blocks H HH _ _ _ _ HP4 ltac:(apply in_or_app; left; exact Hb)) as BR. pose proof BR as (E1 & E2 & E3 & _).
        unfold shavoids. apply Forall_forall. intros iv Hiv.
        exact (djF_inv _ _ _ _ (dj_scratch_placed_sh H HH _ _ _ _ _ (sh Aq) (nsh nq) RFS4 FXS5 BR (sh_mono _ _ ltac:(apply Z.le_refl)) (sh_nsh_sub Aq nq Aq nq ltac:(clear - E1; cbn in E1; lia) ltac:(cbn in E2; exact E2) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(cbn in E3; exact E3))) Hiv). }
      unfold MBL, blocks_MEMBIO in SHV. unfold AAPP_HI in SHV.
      split; [| split; [| split]]; (eapply SHV; [| eassumption|]); [left; reflexivity| clear - G5 ACB; lia| right; left; reflexivity| clear - H5 ACB; lia| right; right; left; reflexivity| clear - I5 ACB; lia| right; right; right; left; reflexivity| clear - K5 ACB; lia]. }
    pose proof (ah_mpres_trans H HH _ _ _ MPc5 (ah_mpres_trans H HH _ _ _ MP6 MP7)) as MPc7.
    clear MPc5 MP6 MP7 W4 HP4 RFS4 ERR4 AUX4 LM4 MI4' AC4' STK4 ST04 CHN4 XA4 LED4 IM4 MFq4 CP4 GM4 MM4 MB4 RL4 KREL5 KREL6 VIS5 VIS6 MI4 AC4 ST4 XP5 HP5 MBq4 MSHb4.
    (* [comment removed for export] *)
    pose proof BB5 as (IF1 & IF2 & IF3 & RG1 & RG2 & RG3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RG1 as (Ba1 & Ba2 & Ba3 & Ba4 & Ba5 & Ba6 & Ba7). pose proof RG2 as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5 & Bc6 & Bc7). pose proof RG3 as (Be1 & Be2 & Be3 & Be4 & Be5 & Be6 & Be7).
    unfold BIO_SIZE in Ba5. unfold B64CTX_SIZE in Bc5.
    pose proof W5 as (HP5w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL5 & _ & _ & _ & _ & _ & RFS5' & [errv5' ERR5'] & AUX5' & LM5 & _ & _ & _ & _ & MI5' & AC5' & STK5 & ST05 & CHN5 & XA5 & LED5).
    pose proof LM5 as (IM5' & MFq5 & CP5' & _ & _ & _ & _ & _ & GM5' & _ & _ & MM5 & MB5' & _ & RL5' & _). rewrite MF1 in MFq5.
    (* [comment removed for export] *)
    assert (APM : Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) MBL) FB).
    { apply Forall_forall. intros b Hb. apply Forall_forall. intros b' Hb'.
      pose proof (perm_split_disjoint H HX _ _ FB (MBL ++ (p, A, nA) :: L0c) _ _ _ HP5' ltac:(unfold TB; rewrite <- app_assoc; apply Permutation_refl) Hb ltac:(apply in_or_app; left; exact Hb')) as K0.
      clear - K0. lia. }
    (* [comment removed for export] *)
    destruct (SLOTS_join _ _ _ _ _ SL5) as (jq & x16 & x24 & x32 & x40 & x48 & x56 & x64 & x72 & x80 & x88 & x192 & x200 & x208 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & _ & P2b).
    eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7| eapply afb_seg4 with (q := S1c) (ff := ff); [clear - APOS5 Ba5 ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2b| exact MI5]|].
    intros msF8 mo8 KREL8 MP8 VIS8. cbn beta in VIS8.
    pose proof (abiosetflags_spec H) as SF. unfold biosetflags_stmt, bioacc_stmt_at in SF.
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply SF with (a := a) (x := 256) (lo := lo) (B := b64f_bio Rf); clear SF;
      [reflexivity| reflexivity| clear; lia| exact BC5| | clear - Ba5 CEIL; unfold BIO_SIZE; lia| exact (proj1 BSH5)| exact RG1| exact AC5
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST5| exact CEIL| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKA Q2; lia| exact MI5| reflexivity]|].
    { unfold bio_ok, b64f_bio. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      rewrite FL0, RT0, NR0, NX0, PV0. unfold A_b64_method. clear - Bc1 Bc5 ACB. repeat split; lia. }
    cbv beta. intros msF9 mo9 KREL9 MP9 (x0 & x1 & x2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & m6 & VIS9 & MU6 & WM6 & MI6 & AC6 & ST6 & BC6).
    rewrite (unsigned_lit S1c) in MU6, ST6 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    unfold b64f_bio in BC6. cbn [bio_with_flags bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC6.
    rewrite FL0, RT0, NR0, NX0, PV0 in BC6. cbn [Z.lor] in BC6.
    change (rw_cells asegs m6 a (bio_cells (b64f_bio (bf_fresh2 Rf 0)))) in BC6.
    assert (INa : In (bf_id Rf, a, BIO_SIZE) (TB ++ (p, A, nA) :: L0c)) by (unfold TB, FB, blocks_B64F; left; reflexivity).
    assert (W6 : CW TB p A nA R' ff fp fk1 fk2 jg e5 n (um + 208 + 2804) uf m6 s5').
    { eapply (cw_ws TB p A nA R' ff fp fk1 fk2 jg e5 n _ uf m5 s5' m6 [(lo, S1c); (a, a + BIO_SIZE)] []);
        [exact W5| rewrite app_nil_r; exact MU6| exact WM6| exact MI6| exact AC6| exact ST6| | | apply Forall_nil].
      - eapply (cw_rfs0 s5' (TB ++ (p, A, nA) :: L0c) _ m5 m6); [exact HP5'| exact RFS5'| exact MU6| exact WM6|].
        apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl|]. apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [exact INa| cbn; split; apply Z.le_refl]| apply Forall_nil].
      - apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl|]. apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [unfold TB, FB, blocks_B64F; left; reflexivity| cbn; split; apply Z.le_refl]| apply Forall_nil]. }
    assert (MBq6 : MEMBIO H MBL m6 mb2 M2).
    { eapply (AMEMBIO_munch H MBL _ m5 m6); [exact MBq5| exact MU6| exact WM6|].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; apply Forall_forall; intros b Hb; cbn [fst snd].
      - left. pose proof (ah_blocks H HH _ _ _ _ HP5' ltac:(apply in_or_app; left; unfold TB; apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & E5 & _). clear - E5 CEIL. lia.
      - pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) APM _ ltac:(unfold FB, blocks_B64F; left; reflexivity)) b Hb) as K0. cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    assert (ADX6 : forall b' Aq nq, In b' (TB ++ (p, A, nA) :: L0c) -> blk_addr b' <= Aq -> Aq + nq <= blk_addr b' + blk_size b' -> 0 <= nq -> addressable m5 Aq nq -> addressable m6 Aq nq).
    { intros b' Aq nq Hb' HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HP5' Hb') as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      eapply addressable_acrossX; [exact AD| exact MU6| exact WM6| clear - E1 HA; lia| unfold AAPP_HI; clear - E5 HB ACB; lia|].
      apply Forall_cons; [apply winX_stk; cbn [fst]; apply Z.le_refl|]. apply Forall_cons; [| apply Forall_nil].
      eapply (winX_blk s5' _ m5 (bf_id Rf, a, BIO_SIZE)); [exact HP5'| exact INa| clear - E1 HA; lia| exact N0| unfold AAPP_HI; clear - E5 HB ACB; lia| cbn; apply Z.le_refl| cbn; apply Z.le_refl]. }
    assert (INmb : forall b', In b' MBL -> In b' (TB ++ (p, A, nA) :: L0c)) by (intros b' Hb'; apply in_or_app; left; unfold TB; apply in_or_app; right; exact Hb').
    assert (INfb : forall b', In b' FB -> In b' (TB ++ (p, A, nA) :: L0c)) by (intros b' Hb'; apply in_or_app; left; unfold TB; apply in_or_app; left; exact Hb').
    assert (MSHb6 : MEMBIO_shad m6 mb2 M2).
    { destruct MSHb5 as (T1 & T2 & T3 & T4). unfold MEMBIO_shad. split; [| split; [| split]].
      - eapply (ADX6 (mb_id M2, mb2, BIO_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact T1].
      - eapply (ADX6 (mb_bbid M2, mb_bb M2, BIOBUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIOBUFMEM_SIZE; clear; lia| exact T2].
      - eapply (ADX6 (mb_bmid M2, mb_bm M2, BUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact T3].
      - eapply (ADX6 (mb_rpid M2, mb_rp M2, BUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact T4]. }
    assert (BSH6 : B64F_shad m6 a Rf).
    { destruct BSH5 as (T1 & T2 & T3). unfold B64F_shad. split; [| split].
      - eapply (ADX6 (bf_id Rf, a, BIO_SIZE)); [apply INfb; unfold FB, blocks_B64F; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact T1].
      - eapply (ADX6 (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE)); [apply INfb; unfold FB, blocks_B64F; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold B64CTX_SIZE; clear; lia| exact T2].
      - eapply (ADX6 (bf_eid Rf, bf_enc Rf, 92)); [apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| clear; lia| exact T3]. }
    assert (CJ6 : rw_cells asegs m6 (bf_ctx Rf) (b64ctx_fresh_cells (bf_enc Rf) cj)).
    { eapply rw_cells_transport; [exact CJ5| exact MU6| exact WM6|]. cbn. pose proof BAP as (AP1 & _). unfold BIO_SIZE, B64CTX_SIZE in *.
      assert (LJ : Z.of_nat (cells_size (b64ctx_fresh_cells (bf_enc Rf) cj)) = 2584) by reflexivity.
      rewrite LJ. clear - Bc5 CEIL AP1. split; [lia| split; [lia| exact I]]. }
    assert (EC6 : ENCCTX H TB m6 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_rebase; [| unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity].
      eapply ENCCTX_transport14; [exact MU6| exact WM6| | exact EC5]. cbn. pose proof BAP as (_ & AP2 & _). unfold BIO_SIZE, ENCCTX_SIZE in *. clear - Be5 CEIL AP2. split; [lia| split; [lia| exact I]]. }
    pose proof (ah_mpres_trans H HH _ _ _ MPc7 (ah_mpres_trans H HH _ _ _ MP8 MP9)) as MPc9.
    clear MPc7 MP8 MP9 W5 HP5w SL5 RFS5' ERR5' AUX5' LM5 MI5' AC5' STK5 ST05 CHN5 XA5 LED5 IM5' MFq5 CP5' GM5' MM5 MB5' RL5' KREL7 KREL8 VIS7 VIS8 MI5 AC5 ST5 ERR5 AUX5 MU6 WM6 BC5 CJ5 EC5 BSH5 MBq5 MSHb5 P2b.
    pose proof W6 as (HP6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS6 & [errv6 ERR6] & AUX6 & LM6 & _ & _ & _ & _ & MI6' & AC6' & STK6 & ST06 & CHN6 & XA6 & LED6).
    pose proof LM6 as (IM6 & MFq6 & _ & _ & _ & _ & _ & _ & GM6 & _ & _ & MM6 & MB6 & _ & RL6 & _). rewrite MF1 in MFq6.
    (* [comment removed for export] *)
    assert (APP : Forall (fun b' => A + nA <= blk_addr b' \/ blk_addr b' + blk_size b' <= A) TB).
    { apply Forall_forall. intros b' Hb'.
      pose proof (perm_split_disjoint H HX _ _ TB ((p, A, nA) :: L0c) _ _ _ HP5' (Permutation_refl _) Hb' (or_introl eq_refl)) as K0. cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    pose proof APP as APP'. unfold TB in APP'. apply Forall_app in APP'. destruct APP' as [APf APm].
    assert (MSEP : MEMBIO_sep mb2 M2).
    { split; [exact MAP2|]. rewrite MBUF, MLEN.
      pose proof (Forall_inv APm) as K1. pose proof (Forall_inv (Forall_inv_tail APm)) as K2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APm))) as K3.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APm)))) as K4.
      cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. pose proof W6 as (_ & _ & _ & _ & LR6 & _). clear - K1 K2 K3 K4 LR6. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. repeat split; lia. }
    assert (MBLO : MEMBIO_below mb2 M2 lo).
    { pose proof MBq6 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & G5 & _) & (_ & _ & _ & _ & H5 & _) & (_ & _ & _ & _ & I5 & _) & (_ & _ & _ & _ & K5 & _) & _).
      unfold MEMBIO_below. clear - G5 H5 I5 K5 CEIL. repeat split; lia. }
    assert (BFL : B64F_below a Rf lo) by (unfold B64F_below; clear - Ba5 Bc5 Be5 CEIL; unfold BIO_SIZE, B64CTX_SIZE; repeat split; lia).
    assert (INm : In (mb_id M2, mb2, BIO_SIZE) (TB ++ (p, A, nA) :: L0c)) by (apply INmb; unfold MBL, blocks_MEMBIO; left; reflexivity).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply afb_seg5; exact MI6|]. intros msF10 mo10 KREL10 MP10 VIS10. cbn beta in VIS10.
    pose proof BPUSH as BP. unfold biopush_stmt in BP.
    eapply (ahh_evt_then H HH); [exact KREL10| exact VIS10| eapply BP with (a := a) (mb := mb2) (lo := lo) (R := bf_fresh2 Rf 0) (M := M2) (LB := TB); clear BP;
      lazymatch goal with
      | |- _ = Z_to_bv _ _ => reflexivity
      | |- B64F_fresh _ _ _ _ _ => split; [exact BC6| split; [exists cj; split; [exact CJL| exact CJ6]| split; [| cbn; clear; repeat split; reflexivity]]];
                                   pose proof BB5 as (_ & _ & _ & REST5); cbn [bf_id bf_cid bf_eid bf_ctx bf_enc bf_flags bf_retry bf_nread bf_next bf_prev bf_fresh2];
                                   split; [apply in_or_app; left; unfold FB, blocks_B64F; left; reflexivity|]; split; [apply in_or_app; left; unfold FB, blocks_B64F; right; left; reflexivity|];
                                   split; [apply in_or_app; left; unfold FB, blocks_B64F; right; right; left; reflexivity|]; split; [exact RG1| split; [exact RG2| split; [exact RG3| cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_fresh2]; clear; repeat split; lia]]]
      | |- B64F_apart _ _ => exact BAP
      | |- bf_next _ = _ => reflexivity
      | |- B64F_below _ _ _ => exact BFL
      | |- MEMBIO _ _ _ _ _ => eapply (MEMBIO_mono H); [exact MBq6| intros b Hb; unfold TB; apply in_or_app; right; exact Hb]
      | |- MEMBIO_below _ _ _ => exact MBLO
      | |- MEMBIO_sep _ _ => exact MSEP
      | |- Forall _ (blocks_B64F _ _) => exact APM
      | |- METH_b64 _ => exact MB6
      | |- METH_mem _ => exact MM6
      | |- B64F_shad _ _ _ => exact BSH6
      | |- MEMBIO_shad _ _ _ => exact MSHb6
      | |- ACONST _ => exact AC6
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST6
      | |- aceil <= lo => exact CEIL
      | |- lo <= _ - _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKP Q2; lia
      | |- mem_inv _ _ => exact MI6
      | |- bv_unsigned _ mod 2 = 0 => reflexivity
      | |- ?G => idtac "BPUSH_LEFT" G
      end|].
    cbv beta. intros msF11 mo11 KREL11 MP11 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m7 & VIS11 & MU7 & WM7 & MI7 & AC7 & ST7 & BF7 & MBO7).
    rewrite (unsigned_lit S1c) in MU7, ST7 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    cbn [bf_flags bf_retry bf_nread bf_prev bf_fresh2] in BF7. change (B64F_fresh H TB m7 a (bf_fresh2 Rf mb2)) in BF7.
    set (M2' := mb_with_hdr M2 (mb_flags M2) (mb_numf M2) (mb_next M2) a) in MBO7.
    assert (FW7 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) [(lo, S1c); (a, a + BIO_SIZE); (mb2, mb2 + BIO_SIZE)]).
    { apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl|]. apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [unfold TB, FB, blocks_B64F; left; reflexivity| cbn; split; apply Z.le_refl]|].
      apply Forall_cons; [right; exists (mb_id M2, mb2, BIO_SIZE); split; [unfold TB; apply in_or_app; right; unfold MBL, blocks_MEMBIO; left; reflexivity| cbn; split; apply Z.le_refl]| apply Forall_nil]. }
    assert (FWL : forall W, Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
                  Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b (TB ++ (p, A, nA) :: L0c) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W).
    { intros W FWq. eapply Forall_impl; [| exact FWq]. cbn beta. intros iv [K|(b & Hb & K1 & K2)]; [left; exact K| right; exists b; split; [apply in_or_app; left; exact Hb| split; [exact K1| exact K2]]]. }
    assert (W7 : CW TB p A nA R' ff fp fk1 fk2 jg e5 n (um + 208 + 2804) uf m7 s5').
    { eapply (cw_ws TB p A nA R' ff fp fk1 fk2 jg e5 n _ uf m6 s5' m7 [(lo, S1c); (a, a + BIO_SIZE); (mb2, mb2 + BIO_SIZE)] []);
        [exact W6| rewrite app_nil_r; exact MU7| exact WM7| exact MI7| exact AC7| exact ST7| | exact FW7| apply Forall_nil].
      eapply (cw_rfs0 s5' (TB ++ (p, A, nA) :: L0c) _ m6 m7); [exact HP6| exact RFS6| exact MU7| exact WM7| exact (FWL _ FW7)]. }
    assert (ADX7 : forall b' Aq nq, In b' (TB ++ (p, A, nA) :: L0c) -> blk_addr b' <= Aq -> Aq + nq <= blk_addr b' + blk_size b' -> 0 <= nq -> addressable m6 Aq nq -> addressable m7 Aq nq).
    { intros b' Aq nq Hb' HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HP6 Hb') as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      eapply addressable_acrossX; [exact AD| exact MU7| exact WM7| clear - E1 HA; lia| unfold AAPP_HI; clear - E5 HB ACB; lia|].
      apply Forall_cons; [apply winX_stk; cbn [fst]; apply Z.le_refl|].
      apply Forall_cons; [eapply (winX_blk s5' _ m6 (bf_id Rf, a, BIO_SIZE)); [exact HP6| exact INa| clear - E1 HA; lia| exact N0| unfold AAPP_HI; clear - E5 HB ACB; lia| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
      apply Forall_cons; [eapply (winX_blk s5' _ m6 (mb_id M2, mb2, BIO_SIZE)); [exact HP6| exact INm| clear - E1 HA; lia| exact N0| unfold AAPP_HI; clear - E5 HB ACB; lia| cbn; apply Z.le_refl| cbn; apply Z.le_refl]| apply Forall_nil]. }
    assert (MSHb7 : MEMBIO_shad m7 mb2 M2').
    { destruct MSHb6 as (T1 & T2 & T3 & T4). unfold MEMBIO_shad. cbn [mb_bb mb_bm mb_rp M2' mb_with_hdr]. split; [| split; [| split]].
      - eapply (ADX7 (mb_id M2, mb2, BIO_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact T1].
      - eapply (ADX7 (mb_bbid M2, mb_bb M2, BIOBUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIOBUFMEM_SIZE; clear; lia| exact T2].
      - eapply (ADX7 (mb_bmid M2, mb_bm M2, BUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact T3].
      - eapply (ADX7 (mb_rpid M2, mb_rp M2, BUFMEM_SIZE)); [apply INmb; unfold MBL, blocks_MEMBIO; right; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact T4]. }
    assert (BSH7 : B64F_shad m7 a Rf).
    { destruct BSH6 as (T1 & T2 & T3). unfold B64F_shad. split; [| split].
      - eapply (ADX7 (bf_id Rf, a, BIO_SIZE)); [apply INfb; unfold FB, blocks_B64F; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact T1].
      - eapply (ADX7 (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE)); [apply INfb; unfold FB, blocks_B64F; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold B64CTX_SIZE; clear; lia| exact T2].
      - eapply (ADX7 (bf_eid Rf, bf_enc Rf, 92)); [apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| clear; lia| exact T3]. }
    assert (EC7 : ENCCTX H TB m7 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_transport14; [exact MU7| exact WM7| | exact EC6]. cbn. pose proof BAP as (_ & AP2 & _).
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) APM _ ltac:(unfold FB, blocks_B64F; right; right; left; reflexivity)) _ ltac:(unfold MBL, blocks_MEMBIO; left; reflexivity)) as K0.
      cbn [blk_addr blk_size fst snd] in K0. unfold BIO_SIZE, ENCCTX_SIZE in *. clear - Be5 CEIL AP2 K0. split; [lia| split; [lia| split; [lia| exact I]]]. }
    pose proof (ah_mpres_trans H HH _ _ _ MPc9 (ah_mpres_trans H HH _ _ _ MP10 MP11)) as MPc11.
    clear MPc9 MP10 MP11 W6 HP6 RFS6 ERR6 AUX6 LM6 MI6' AC6' STK6 ST06 CHN6 XA6 LED6 IM6 MFq6 GM6 MM6 MB6 RL6 KREL9 KREL10 VIS9 VIS10 MI6 AC6 ST6 MU7 WM7 BC6 CJ6 EC6 BSH6 MBq6 MSHb6 ADX6 ADX7 FW7.
    pose proof W7 as (HP7 & _ & _ & _ & LR7 & _ & LT7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS7 & [errv7 ERR7] & AUX7 & LM7 & _ & _ & _ & _ & MI7' & AC7' & STK7 & ST07 & CHN7 & XA7 & LED7).
    pose proof LM7 as (IM7 & MFq7 & _ & _ & _ & _ & _ & _ & GM7 & _ & _ & MM7 & MB7 & _ & RL7 & _). rewrite MF1 in MFq7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL11| exact VIS11| eapply afb_seg6; exact MI7|]. intros msF12 mo12 KREL12 MP12 VIS12. cbn beta in VIS12.
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_seq H HH).
    { eapply CM with (n := mb_len R) (lo := lo) (B := B) (LB := TB ++ (p, A, nA) :: L0c) (s := s5') (v := 1) (errv := errv7) (CH := CH1c); clear CM.
      all: try first [exact VIS12| exact HP7| exact KREL12| exact AUX7| exact MI7| exact IM7| exact GM7| exact MFq7| exact CEIL| exact AC7| exact CHN7| exact ERR7].
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
           | |- 1 <= mb_len R < _ => clear - LR7 LT7; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in LT7; lia
           | |- 1 <= mb_len R <= _ => clear - LR7 LT7; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in LT7; lia
           | |- lb_bytes _ + _ <= _ => unfold TB; rewrite !lb_bytes_app, lb_bytes_cons; cbn [blk_size snd]; unfold MBL; rewrite (proj1 (membio_blocks_facts mb2 M2)); unfold FB; rewrite (proj2 (blocks_B64F_facts a Rf));
                 pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq; unfold DECODE_BYTES, ERRSTR_BYTES, MEMBIO_BYTES, B64F_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, B64CTX_SIZE in *; unfold L0; clear - BUDq NAR LR7 LT7 EBR; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold TB; rewrite !length_app; cbn [length]; unfold MBL, blocks_MEMBIO, FB, blocks_B64F; cbn [length Nat.add]; pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq; unfold L0; clear - BUDq ECR; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK7
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKM Q2; lia
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
           | |- pf_ok _ _ _ _ => unfold AFB_R6; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 12 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- as_Cm H _ <= as_AL H _ => destruct LED7 as (L0' & L1' & L2');
                 pose proof ((RCI LEDGER_pay) s5' (um + 208 + 2804) uf (mb_len R) 0 (conj L0' (conj L1' L2')) ltac:(clear - LR7; lia) ltac:(clear; lia)
                               ltac:(unfold FMT_UM, lad_cm, DECODE_CUM_BYTES, OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - UMB LT7; lia) ltac:(unfold FMT_UF, lad_cf, DECODE_CUM_BYTES in *; clear - UFB; lia)) as PY;
                 pose proof (CF0 0 ltac:(clear; lia)) as Y3; clear - PY Y3; lia
           | |- bv_unsigned _ mod 2 = 0 => reflexivity
           | |- ?G => idtac "CM_LEFT" G
           end. }
    clear CM. intros [msF13 mo13] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0' & v1' & v2' & k1 & k2 & k3 & k4 & k5 & k6 & k7 & v3' & v4' & v5' & v6' & m8 & errv8 & Bb & junk8 & pbin & s8' & VIS13 & KREL13 & MP13 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & BRB & HP8 & CELLS8 & ADB8 & MF8 & IM8 & GM8 & AL8).
    rewrite (unsigned_lit S1c) in ST8, XP8 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    pose proof BRB as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6 & Bb7). unfold AIMG_TOP in Bb4.
    assert (XP8n : xpres H (TB ++ (p, A, nA) :: L0c) S1c [] m7 m8).
    { apply (ECH_AC14_kit.axpres_drop_memflag H _ S1c [] [] m7 m8 MFq7 MF8). cbn [app]. rewrite app_nil_r. exact XP8. }
    assert (W8 : CW ((pbin, Bb, mb_len R) :: TB) p A nA R' ff fp fk1 fk2 jg e5 n (um + 208 + 2804 + mb_len R) uf m8 s8').
    { eapply (cw_xs TB ((pbin, Bb, mb_len R) :: TB) p A nA R' ff fp fk1 fk2 jg e5 n _ uf _ uf m7 s5' m8 s8' []);
        [exact W7| rewrite app_nil_r; exact XP8| apply Forall_nil| exact MF8| cbn [app]; exact HP8| intros b Hb; right; exact Hb| exact MI8| exact AC8| exact ST8| exact AUX8| exact ERR8| |].
      - eapply (ECH_AKit.RFS_via_xpres H HH); [exact RFS7| exact XP8| unfold memflag_foot; apply Forall_cons; [cbn [snd]; unfold A_mem_inited, ATLS_PRIV_LO, ATP; clear; lia| apply Forall_nil]].
      - pose proof ((RCI LEDGER_step) s5' s8' (um + 208 + 2804) uf (mb_len R) 0 LED7 ltac:(clear - LR7; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS. clear LS.
        pose proof (CF0 0 ltac:(clear; lia)) as Y3. clear - AL8 Y3. lia. }
    (* [comment removed for export] *)
    set (L8 := (pbin, Bb, mb_len R) :: TB ++ (p, A, nA) :: L0c) in *.
    assert (IN78 : forall b, In b (TB ++ (p, A, nA) :: L0c) -> In b L8) by (intros b Hb; right; exact Hb).
    assert (MBO8 : MEMBIO H TB m8 mb2 M2').
    { eapply (AMEMBIO_xpres H TB (TB ++ (p, A, nA) :: L0c) S1c [] m7 m8); [exact MBO7| intros b Hb; apply INmb; exact Hb| exact XP8n| apply Forall_nil]. }
    assert (BF8 : B64F_fresh H TB m8 a (bf_fresh2 Rf mb2)).
    { eapply B64F_fresh_xpres0; [exact BF7| exact XP8n| exact INa| apply INfb; unfold FB, blocks_B64F; right; left; reflexivity]. }
    assert (EC8 : ENCCTX H TB m8 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_xpresX; [exact EC7| exact XP8n| apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| unfold avoids; apply Forall_nil]. }
    assert (ADX8 : forall q Aq nq, In (q, Aq, nq) (TB ++ (p, A, nA) :: L0c) -> addressable m7 Aq nq -> addressable m8 Aq nq).
    { intros q Aq nq Hb AD. pose proof (ah_blocks H HH _ _ _ _ HP7 Hb) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E5.
      eapply (addressable_xpres_blkX H (TB ++ (p, A, nA) :: L0c) m7 m8 S1c [] q); [exact Hb| unfold AAPP_HI; clear - E5 ACB; lia| exact AD| exact XP8n| unfold shavoids; apply Forall_nil]. }
    assert (MSHb8 : MEMBIO_shad m8 mb2 M2').
    { destruct MSHb7 as (T1 & T2 & T3 & T4). unfold MEMBIO_shad. cbn [mb_bb mb_bm mb_rp M2' mb_with_hdr] in T2, T3, T4 |- *. split; [| split; [| split]].
      - eapply ADX8; [apply INmb; unfold MBL, blocks_MEMBIO; left; reflexivity| exact T1].
      - eapply ADX8; [apply INmb; unfold MBL, blocks_MEMBIO; right; left; reflexivity| exact T2].
      - eapply ADX8; [apply INmb; unfold MBL, blocks_MEMBIO; right; right; left; reflexivity| exact T3].
      - eapply ADX8; [apply INmb; unfold MBL, blocks_MEMBIO; right; right; right; left; reflexivity| exact T4]. }
    assert (BSH8 : B64F_shad m8 a Rf).
    { destruct BSH7 as (T1 & T2 & T3). unfold B64F_shad. split; [| split].
      - eapply ADX8; [apply INfb; unfold FB, blocks_B64F; left; reflexivity| exact T1].
      - eapply ADX8; [apply INfb; unfold FB, blocks_B64F; right; left; reflexivity| exact T2].
      - eapply ADX8; [apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| exact T3]. }
    pose proof (ah_mpres_trans H HH _ _ _ MPc11 (ah_mpres_trans H HH _ _ _ MP12 MP13)) as MPc13.
    clear MPc11 MP12 MP13 W7 HP7 RFS7 ERR7 AUX7 LM7 MI7' AC7' STK7 ST07 CHN7 XA7 LED7 IM7 MFq7 GM7 MM7 MB7 RL7 KREL11 KREL12 VIS11 VIS12 MI7 AC7 ST7 XP8 XP8n BF7 MBO7 EC7 MSHb7 BSH7 ADX8 MBLO.
    pose proof W8 as (HP8' & _ & MST8 & POS8 & LR8 & NAR8 & LT8 & DSm8 & DSA8 & _ & ADA8 & _ & _ & _ & FRESH8 & _ & _ & RFS8 & [errv8' ERR8'] & AUX8' & LM8 & _ & _ & _ & _ & MI8' & AC8' & STK8 & ST08 & CHN8 & XA8 & LED8).
    cbn [app] in HP8'. fold L8 in HP8'.
    pose proof LM8 as (IM8' & MFq8 & _ & _ & _ & _ & _ & _ & GM8' & _ & _ & MM8 & MB8 & _ & RL8 & _). rewrite MF1 in MFq8.
    pose proof (ah_blocks H HH _ _ _ _ HP8' ltac:(unfold L8; right; apply in_or_app; right; left; reflexivity)) as (LA1 & LA2 & LA3 & LA4 & LA5 & LA6 & LA7). cbn [blk_addr blk_size fst snd] in LA1, LA2, LA3, LA4, LA5, LA6, LA7.
    (* [comment removed for export] *)
    assert (APB : Forall (fun b => Bb + mb_len R <= blk_addr b \/ blk_addr b + blk_size b <= Bb) TB).
    { apply Forall_forall. intros b' Hb'.
      pose proof (perm_split_disjoint H HX _ _ [(pbin, Bb, mb_len R)] (TB ++ (p, A, nA) :: L0c) _ _ _ HP8' (Permutation_refl _) (or_introl eq_refl) ltac:(apply in_or_app; left; exact Hb')) as K0.
      cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    pose proof APB as APB'. unfold TB in APB'. apply Forall_app in APB'. destruct APB' as [APBf APBm].
    assert (DAB : A + nA <= Bb \/ Bb + mb_len R <= A).
    { pose proof (perm_split_disjoint H HX _ _ [(pbin, Bb, mb_len R)] (TB ++ (p, A, nA) :: L0c) _ _ _ HP8' (Permutation_refl _) (or_introl eq_refl) ltac:(apply in_or_app; right; left; reflexivity)) as K0.
      cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    assert (MBLO : MEMBIO_below mb2 M2' lo).
    { pose proof MBO8 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & G5 & _) & (_ & _ & _ & _ & H5 & _) & (_ & _ & _ & _ & I5 & _) & (_ & _ & _ & _ & K5 & _) & _).
      cbn [mb_bb mb_bm mb_rp M2' mb_with_hdr] in H5, I5, K5. unfold MEMBIO_below. cbn [mb_bb mb_bm mb_rp M2' mb_with_hdr]. clear - G5 H5 I5 K5 CEIL. repeat split; lia. }
    assert (MSEP' : MEMBIO_sep mb2 M2') by exact MSEP.
    assert (MRO : memrd_out mb2 M2' Bb (mb_len R) lo S1c).
    { unfold memrd_out. cbn [mb_buf mb_len M2' mb_with_hdr blocks_MEMBIO mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp]. rewrite MBUF, MLEN.
      split; [left; clear - Bb5 CEIL; lia|]. split; [exact Bb1|]. split; [clear - Bb5 ACB; lia|]. split; [exact APBm|].
      split; [clear - DAB LR8; lia|]. unfold A_mem_buf_method, O_METH_BREAD. clear - Bb4. lia. }
    assert (PSH8 : PAYLOAD_shad m8 M2').
    { unfold PAYLOAD_shad. cbn [mb_buf mb_len M2' mb_with_hdr]. rewrite MBUF, MLEN. split; [| split].
      - eapply (addressable_accessible _ _ _ _ _ ADA8); [apply Z.le_refl| clear - LR8; lia| unfold AAPP_HI; clear - LA5 ACB; lia].
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP8' ltac:(unfold L8; right; apply in_or_app; right; left; reflexivity))| clear - LA1; lia| apply Z.le_refl| clear - LR8; lia| clear - LR8; lia| clear - LA1 LR8; lia].
      - eapply aapp_in_app_mem; [exact LA7| apply Z.le_refl| clear - LR8; lia]. }
    assert (OSH8 : OUT_shad m8 Bb (mb_len R)).
    { unfold OUT_shad. split; [| split; [| split]].
      - eapply (addressable_accessible _ _ _ _ _ ADB8); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI; clear - Bb5 ACB; lia].
      - exact (ah_blk_shvis H HH _ _ _ _ _ _ HP8' ltac:(unfold L8; left; reflexivity)).
      - eapply aapp_in_app_mem; [exact Bb7| apply Z.le_refl| apply Z.le_refl].
      - eapply aconst_ok_aapp; [exact Bb7| apply Z.le_refl| apply Z.le_refl]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL13| exact VIS13| eapply afb_seg7; [clear - Bb1 Bb5 ACB LR8; lia| exact MI8]|]. intros msF14 mo14 KREL14 MP14 VIS14. cbn beta in VIS14.
    pose proof BREAD as BRD. unfold bioread_b64_stmt in BRD.
    eapply (ahh_evt_then H HH); [exact KREL14| exact VIS14| eapply BRD with (LB := L8) (LF := LF1c ff fp) (sA := s8') (a := a) (mb := mb2) (out := Bb) (outl := mb_len R) (lo := lo) (R := bf_fresh2 Rf mb2) (M := M2') (txt := ds) (junk := junk8); clear BRD;
      lazymatch goal with
      | |- _ = Z_to_bv _ _ => reflexivity
      | |- 0 < mb_len R < _ => clear - LR8 LT8; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in LT8; lia
      | |- B64F_fresh _ _ _ _ _ => eapply B64F_fresh_mono; [exact BF8| intros b Hb; apply IN78; apply INfb; exact Hb]
      | |- B64F_apart _ _ => exact BAP
      | |- bf_next _ = _ => reflexivity
      | |- B64F_below _ _ _ => exact BFL
      | |- ENCCTX _ _ _ _ _ _ => eapply ENCCTX_rebase; [exact EC8| apply IN78; apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity]
      | |- MEMBIO _ _ _ _ _ => eapply (MEMBIO_mono H); [exact MBO8| intros b Hb; apply IN78; apply in_or_app; left; exact Hb]
      | |- mb_pos _ = 0 => exact MPOS
      | |- MEMBIO_below _ _ _ => exact MBLO
      | |- MEMBIO_sep _ _ => exact MSEP'
      | |- bytes_at _ _ _ _ => cbn [mb_buf M2' mb_with_hdr]; rewrite MBUF; exact DSA8
      | |- zlength ds = _ => cbn [mb_len M2' mb_with_hdr]; rewrite MLEN; exact DSL
      | |- zlength ds <= _ => rewrite DSL; apply Z.le_refl
      | |- rw_cells _ _ Bb _ => exact CELLS8
      | |- memrd_out _ _ _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact MRO
      | |- Bb + _ <= A_b64_method + _ \/ _ => unfold A_b64_method, O_METH_BREAD; clear - Bb4; lia
      | |- Forall _ (blocks_B64F _ _) => first [exact APBf| exact APM| cbn [mb_buf mb_len M2' mb_with_hdr]; rewrite MBUF, MLEN; eapply Forall_impl; [| exact APf]; cbn beta; intros b0 Hb0; clear - Hb0 LR8; lia]
      | |- METH_b64 _ => exact MB8
      | |- METH_mem _ => exact MM8
      | |- B64F_shad _ _ _ => exact BSH8
      | |- MEMBIO_shad _ _ _ => exact MSHb8
      | |- PAYLOAD_shad _ _ => exact PSH8
      | |- OUT_shad _ _ _ => exact OSH8
      | |- ACONST _ => exact AC8
      | |- arelro_lib _ => exact RL8
      | |- as_RFS _ _ _ => exact RFS8
      | |- (length _ + 2 < _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; clear - LFB; lia
      | |- Z_to_bv 64 ATP = _ => reflexivity
      | |- as_RHEAP _ _ _ _ => exact HP8'
      | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
      | |- fsobj _ _ Bb _ => eapply (fsobj_block H HH); [exact HP8'| unfold L8; left; reflexivity]
      | |- fsobj _ _ _ _ => cbn [mb_buf mb_len M2' mb_with_hdr]; rewrite MBUF, MLEN; apply (fsobj_outside H); clear - LA6 LR8; unfold AFS_SIZE in *; lia
      | |- afs_write_ok _ _ _ => left; cbn [fst snd]; split; [clear - Bb6; unfold AFS_SIZE in *; lia| right; unfold ATLS_PRIV_HI, ATP; clear - Bb4; lia]
      | |- aclient_write_ok _ _ _ => right; right; left; exists (pbin, Bb, mb_len R); split; [unfold L8; left; reflexivity| cbn; split; apply Z.le_refl]
      | |- AIMG_TOP <= Bb => unfold AIMG_TOP; exact Bb4
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST8
      | |- aceil <= lo => exact CEIL
      | |- lo <= _ - _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKR Q2; lia
      | |- mem_inv _ _ => exact MI8
      | |- bv_unsigned _ mod 2 = 0 => reflexivity
      | |- ?G => idtac "BRD_LEFT" G
      end|].
    cbv beta. intros msF15 mo15 KREL15 MP15 PO. unfold bioread_b64_post in PO. cbv zeta in PO.
    destruct PO as (r0 & r1 & r2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & r3 & r4 & r5 & r6 & m9 & R9 & d9 & M9 & junk9 & XS9 & VIS15 & FXS9 & MU9 & WM9 & MI9 & AC9 & ST9 & BU9 & BLK9 & NX9 & EC9 & MBO9 & MBK9 & MBF9 & MLN9 & MNX9 & DSA9 & OUT9 & RFS9 & RL9 & HP9).
    rewrite (unsigned_lit S1c) in MU9, ST9 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned ds) (mb_len R)) in *.
    assert (RVF : (br_rv res = Z.of_nat (length (br_out res)) \/ (br_rv res = -1 /\ br_out res = [])) /\ Z.of_nat (length (br_out res)) <= mb_len R)
      by (apply b64_read_rv; clear - LR8; lia).
    (* [comment removed for export] *)
    set (W0 := [(lo, S1c); (Bb, Bb + mb_len R)] ++ (B64F_foot a (bf_fresh2 Rf mb2) ++ MEMBIO_foot mb2 M2')).
    assert (MU9' : munch (W0 ++ XS9) m8 m9).
    { eapply munch_incl; [exact MU9|]. intros q Hq. change (rin_ivs ([(lo, S1c); (Bb, Bb + mb_len R)] ++ XS9 ++ B64F_foot a (bf_fresh2 Rf mb2) ++ MEMBIO_foot mb2 M2') q) in Hq.
      subst W0. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [right; exact Hq| left; apply rin_ivs_app; right; exact Hq]. }
    assert (FW9 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (exists b, In b ((pbin, Bb, mb_len R) :: TB) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W0).
    { subst W0. apply Forall_cons; [left; cbn [fst snd]; split; apply Z.le_refl|]. apply Forall_cons; [right; exists (pbin, Bb, mb_len R); split; [left; reflexivity| cbn; split; apply Z.le_refl]|].
      unfold B64F_foot, MEMBIO_foot. cbn [bf_ctx bf_enc bf_fresh2 mb_bm M2' mb_with_hdr app].
      apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; left; reflexivity| cbn; split; apply Z.le_refl]|].
      apply Forall_cons; [right; exists (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; right; left; reflexivity| cbn; split; apply Z.le_refl]|].
      apply Forall_cons; [right; exists (bf_eid Rf, bf_enc Rf, 92); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity| cbn; split; apply Z.le_refl]|].
      apply Forall_cons; [right; exists (mb_id M2, mb2, BIO_SIZE); split; [right; unfold TB, MBL, blocks_MEMBIO; apply in_or_app; right; left; reflexivity| cbn; split; apply Z.le_refl]|].
      apply Forall_cons; [right; exists (mb_bmid M2, mb_bm M2, BUFMEM_SIZE); split; [right; unfold TB, MBL, blocks_MEMBIO; apply in_or_app; right; right; right; left; reflexivity| cbn; split; apply Z.le_refl]| apply Forall_nil]. }
    assert (W9 : CW ((pbin, Bb, mb_len R) :: TB) p A nA R' ff fp fk1 fk2 jg e5 n (um + 208 + 2804 + mb_len R) uf m9 s8').
    { eapply (cw_ws ((pbin, Bb, mb_len R) :: TB) p A nA R' ff fp fk1 fk2 jg e5 n _ uf m8 s8' m9 W0 XS9);
        [exact W8| exact MU9'| exact WM9| exact MI9| exact AC9| exact ST9| exact RFS9| exact FW9| exact FXS9]. }
    (* [comment removed for export] *)
    assert (ADX9 : forall b' Aq nq, In b' L8 -> blk_addr b' <= Aq -> Aq + nq <= blk_addr b' + blk_size b' -> 0 <= nq -> addressable m8 Aq nq -> addressable m9 Aq nq).
    { intros b' Aq nq Hb' HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HP8' Hb') as BR'. pose proof BR' as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      assert (A0q : 0 <= Aq) by (clear - E1 HA; lia). assert (TOP : Aq + nq <= AAPP_HI) by (unfold AAPP_HI; clear - E5 HB ACB; lia).
      eapply addressable_acrossX; [exact AD| exact MU9| exact WM9| exact A0q| exact TOP|].
      assert (WB : forall b0 l h, In b0 L8 -> blk_addr b0 <= l -> h <= blk_addr b0 + blk_size b0 -> winX Aq nq (l, h)).
      { intros b0 l h Hb0 K1 K2. eapply (winX_blk s8' L8 m8 b0); [exact HP8'| exact Hb0| exact A0q| exact N0| exact TOP| exact K1| exact K2]. }
      apply Forall_cons; [apply winX_stk; cbn [fst]; apply Z.le_refl|].
      apply Forall_cons; [eapply (WB (pbin, Bb, mb_len R)); [unfold L8; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
      apply Forall_app. split.
      - apply Forall_forall. intros iv Hiv. unfold winX.
        pose proof (djF_inv _ _ _ _ (dj_scratch_placed_sh H HH _ _ _ _ _ (sh Aq) (nsh nq) RFS8 FXS9 BR' (sh_mono _ _ HA) (sh_nsh_sub (blk_addr b') (blk_size b') Aq nq ltac:(clear - E1; lia) E2 HA HB N0)) Hiv) as K.
        clear - K. lia.
      - unfold B64F_foot, MEMBIO_foot. cbn [bf_ctx bf_enc bf_fresh2 mb_bm M2' mb_with_hdr app].
        apply Forall_cons; [eapply (WB (bf_id Rf, a, BIO_SIZE)); [apply IN78; exact INa| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
        apply Forall_cons; [eapply (WB (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE)); [apply IN78; apply INfb; unfold FB, blocks_B64F; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
        apply Forall_cons; [eapply (WB (bf_eid Rf, bf_enc Rf, 92)); [apply IN78; apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
        apply Forall_cons; [eapply (WB (mb_id M2, mb2, BIO_SIZE)); [apply IN78; exact INm| cbn; apply Z.le_refl| cbn; apply Z.le_refl]|].
        apply Forall_cons; [eapply (WB (mb_bmid M2, mb_bm M2, BUFMEM_SIZE)); [apply IN78; apply INmb; unfold MBL, blocks_MEMBIO; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl]| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m9 Bb [CB (length (br_out res)) (map (Z_to_bv 8) (br_out res))] [CB _ junk9]) OUT9) as [OUTa _].
    destruct (rw_cells_CB_bytes_at14 _ _ _ _ _ OUTa) as [BS9 _].
    set (bs := map (Z_to_bv 8) (br_out res)) in *.
    assert (ZL : zlength bs = Z.of_nat (length (br_out res))) by (unfold zlength, bs; rewrite length_map; reflexivity).
    assert (LBS : length bs = length (br_out res)) by (unfold bs; apply length_map).
    rewrite <- LBS in OUT9.
    (* [comment removed for export] *)
    pose proof BLK9 as BLK9'. unfold blocks_B64F in BLK9'. cbn [bf_id bf_cid bf_eid bf_ctx bf_enc bf_fresh2] in BLK9'. injection BLK9' as Eid Ecid Ectx Eeid Eenc.
    pose proof MBK9 as MBK9'. unfold blocks_MEMBIO in MBK9'. cbn [mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp M2' mb_with_hdr] in MBK9'. injection MBK9' as Mid Mbbid Mbb Mbmid Mbm Mrpid Mrp.
    cbn [mb_next M2' mb_with_hdr] in MNX9.
    assert (BT9 : chainBT H TB a mb2 FB MBL m9).
    { exists R9, d9, M9. destruct BSH8 as (T1 & T2 & T3). destruct MSHb8 as (U1 & U2 & U3 & U4). cbn [mb_bb mb_bm mb_rp M2' mb_with_hdr] in U2, U3, U4.
      repeat match goal with |- _ /\ _ => split end.
      - eapply B64F_used_rebase; [exact BU9| rewrite BLK9; intros b Hb; unfold TB; apply in_or_app; left; exact Hb].
      - rewrite BLK9. reflexivity.
      - exact NX9.
      - rewrite Eenc, Eeid. eapply ENCCTX_rebase; [exact EC9| unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity].
      - unfold B64F_apart. rewrite Ectx, Eenc. exact BAP.
      - unfold B64F_shad. rewrite Ectx, Eenc. split; [| split].
        + eapply (ADX9 (bf_id Rf, a, BIO_SIZE)); [apply IN78; exact INa| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact T1].
        + eapply (ADX9 (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE)); [apply IN78; apply INfb; unfold FB, blocks_B64F; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold B64CTX_SIZE; clear; lia| exact T2].
        + eapply (ADX9 (bf_eid Rf, bf_enc Rf, 92)); [apply IN78; apply INfb; unfold FB, blocks_B64F; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| clear; lia| exact T3].
      - eapply (MEMBIO_mono H); [eapply MEMBIO_self; exact MBO9| rewrite MBK9; intros b Hb; unfold TB; apply in_or_app; right; exact Hb].
      - rewrite MBK9. reflexivity.
      - rewrite MNX9. exact MNX.
      - unfold MEMBIO_apart. rewrite Mbb, Mbm, Mrp. exact MAP2.
      - unfold MEMBIO_shad. rewrite Mbb, Mbm, Mrp. split; [| split; [| split]].
        + eapply (ADX9 (mb_id M2, mb2, BIO_SIZE)); [apply IN78; exact INm| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact U1].
        + eapply (ADX9 (mb_bbid M2, mb_bb M2, BIOBUFMEM_SIZE)); [apply IN78; apply INmb; unfold MBL, blocks_MEMBIO; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BIOBUFMEM_SIZE; clear; lia| exact U2].
        + eapply (ADX9 (mb_bmid M2, mb_bm M2, BUFMEM_SIZE)); [apply IN78; apply INmb; unfold MBL, blocks_MEMBIO; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact U3].
        + eapply (ADX9 (mb_rpid M2, mb_rp M2, BUFMEM_SIZE)); [apply IN78; apply INmb; unfold MBL, blocks_MEMBIO; right; right; right; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact U4]. }
    assert (ADB9 : addressable m9 Bb (mb_len R)) by (eapply (ADX9 (pbin, Bb, mb_len R)); [unfold L8; left; reflexivity| cbn; apply Z.le_refl| cbn; apply Z.le_refl| clear - LR8; lia| exact ADB8]).
    (* [comment removed for export] *)
    assert (BTR : 0 <= a < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072).
    { unfold TB. rewrite length_app, lb_bytes_app, Nat2Z.inj_add. unfold FB. rewrite (proj1 (blocks_B64F_facts a Rf)), (proj2 (blocks_B64F_facts a Rf)). unfold MBL. rewrite (proj1 (membio_blocks_facts mb2 M2)), (proj2 (membio_blocks_facts mb2 M2)).
      unfold B64F_BYTES, MEMBIO_BYTES, BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. clear - APOS5 Ba5 ACB. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (BTF : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
              chainBT H TB a mb2 FB MBL m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
              (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> chainBT H TB a mb2 FB MBL m2).
    { intros L1 SP1 X1 ma mb' C1 X2 SB1 CE1 F1 MI1x. unfold TB in *. eapply chainBT_frame; [exact C1| exact X2| exact SB1| exact CE1| exact F1| exact MI1x]. }
    assert (NAR9 : 1 <= mb_len R <= nA /\ nA <= 512 * 3) by (clear - LR8 NAR8; lia).
    assert (NBR9 : 0 <= zlength bs <= mb_len R /\ mb_len R <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN) by (rewrite ZL; clear - RVF LT8; lia).
    clear W8 RFS8 ERR8' AUX8' LM8 MI8' AC8' STK8 ST08 CHN8 XA8 LED8 IM8' MFq8 GM8' MM8 MB8 RL8 KREL13 KREL14 VIS13 VIS14 MI8 AC8 ST8 ERR8 AUX8 MU9 MU9' WM9 OUTa BSH8 MSHb8 PSH8 OSH8 MRO MBO8 BF8 EC8 CELLS8 BU9 EC9 MBO9 FW9.
    (* [comment removed for export] *)
    pose proof W9 as (HP9' & MBOr9 & MST9 & POS9 & LR9 & NARn9 & LT9 & DSm9 & DSA9' & JK9 & ADA9 & SL9 & GP9 & SV9 & FRESH9 & FRM9 & FSH9 & RFS9' & ERR9 & AUX9 & LM9
                      & SC9 & SAD9 & MSH9 & PAYa9 & MI9' & AC9' & STK9 & ST09 & CHN9 & XA9 & LED9).
    cbn [app] in HP9'.
    clear jq x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 x192 x200 x208 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336.
    destruct SL9 as (jz & x16 & x24 & x32 & x40 & x48 & x56 & x64 & x72 & x80 & x88 & x192 & x200 & x208 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & P0 & P1 & P2 & P3).
    destruct (fframe_to2 _ _ _ _ _ _ _ FRM9) as (tpl & fj24 & tpb & fj128 & FRM9' & TPLR).
    pose proof (errblocks_bounds _ _ _ LM9) as [EC9' EB9'].
    pose proof SSH as SSHq. rewrite SEQ in SSHq. apply (proj1 (STORE_shad_empty _ _ _)) in SSHq. destruct SSHq as [SThi _].
    set (um9 := um + 208 + 2804 + mb_len R) in *.
    assert (DW9 : (DCW adwkG) p A nA pbin Bb (mb_len R) bs R' TB (chainBT H TB a mb2 FB MBL) ff fp n fj24 tpb fj128 fk2 jz jg e5 [] [] S M []
                    (arp_sg1 x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))) (wz ARP_FILE) x192 x200 x208 x224 x232
                    (arp_sg3 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336)
                    tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um9 uf m9 s8').
    { unfold adwkG.
      split. { eapply PERM; [exact HP9'|]. unfold drest, L0. cbn [app].
               (* [comment removed for export] *)
               transitivity ((pbin, Bb, mb_len R) :: (mid_errblocks M ++ TB) ++ (p, A, nA) :: LB).
               - apply perm_skip. transitivity ((p, A, nA) :: TB ++ mid_errblocks M ++ LB); [apply Permutation_sym; apply Permutation_middle|].
                 transitivity ((p, A, nA) :: (mid_errblocks M ++ TB) ++ LB); [| apply Permutation_middle]. apply perm_skip.
                 rewrite (app_assoc TB). apply Permutation_app_tail. apply Permutation_app_comm.
               - rewrite (app_assoc (mid_errblocks M) TB). apply (Permutation_middle (mid_errblocks M ++ TB)). }
      split; [exact LM9|].
      split; [unfold mid_step; split; [exact MF1| split; [intros b Hb; exact Hb| split; [intros c Hc; exact Hc| intros Hv; exact Hv]]]|].
      split; [unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl| split; [rewrite CTX; reflexivity| destruct (mid_err M); reflexivity]]|].
      split; [reflexivity|].
      split; [exact EC9'|]. split; [exact EB9'|].
      split; [cbn [length Z.of_nat]; clear; lia|]. split; [change (lb_bytes []) with 0; clear; lia|].
      split; [rewrite SEQ; unfold STOREobj; cbn [es_entries es_entries_o es_id store_empty app]; split; [exact SC9| split; [exact (proj1 (proj2 SO))| reflexivity]]|].
      split; [rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SThi| exact SAD9]|].
      split; [reflexivity|].
      split; [rewrite SEQ; unfold blocks_STORE; cbn [es_entries_o es_id store_empty]; apply Permutation_refl|].
      split; [rewrite SEQ; unfold blocks_STORE; cbn [es_entries_o es_id store_empty map blk_id fst]; constructor; [intros []| constructor]|].
      split; [intros K es E; rewrite SEO in E; discriminate|].
      split; [exact MBOr9|]. split; [exact MSH9|]. split; [exact DSm9|].
      split; [exact BS9|].
      split; [exists junk9; exact OUT9|]. split; [exact ADB9|].
      split; [exact JK9|]. split; [exact ADA9|].
      split; [exact BT9|].
      split; [exact P0|]. split; [exact P1|]. split; [reflexivity|]. split; [unfold dsg2; exact P2|]. split; [exact P3|]. split; [reflexivity|].
      split; [exact GP9|]. split; [exact SV9|].
      split; [unfold dff; exact FRM9'|]. split; [unfold dfsh; exact FSH9|]. split; [reflexivity|]. split; [exact RFS9'|].
      split; [exact ERR9|]. split; [exact AUX9|]. split; [exact MI9'|]. split; [exact AC9'|]. split; [exact STK9|]. split; [exact ST09|].
      split; [exact CHN9|]. split; [exact XA9| exact LED9]. }
    assert (LBE0 : 0 <= lb_bytes (mid_errblocks M)).
    { apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    assert (BD9 : forall hb hc, hb <= DLOOP_BYTES -> hc <= DLOOP_CNT -> dbud H (drest LB p A nA pbin Bb (mb_len R) TB [] [] []) M hb hc).
    { intros hb hc HB HC. clearbody TB. unfold dbud, drest. cbn [app]. rewrite !lb_bytes_app, !lb_bytes_cons, !length_app. cbn [length blk_size snd]. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ.
      pose proof BUD as BUDq. pose proof BUDC as BUCq. unfold mid_bytes in BUDq. unfold mid_cnt in BUCq. rewrite CTX in BUDq, BUCq. cbn [ctxph_bytes ctxph_cnt] in BUDq, BUCq.
      rewrite lb_bytes_app in BUDq. rewrite length_app, Nat2Z.inj_add in BUCq. destruct BTR as (_ & TL & TBY).
      unfold DECODE_BYTES, DECODE_CNT, DLOOP_BYTES, DLOOP_CNT, OSSL_ECH_MAX_ECHCONFIG_LEN in *. clear - HB HC BUDq BUCq TL TBY NAR9 LT9 LBE0. split; lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL15| exact VIS15| eapply afb_seg8 with (q := S1c); [clear - RVF LT9; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in LT9; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2| exact MI9]|].
    intros msF16 mo16 KREL16 MP16. cbn beta. pose proof (ah_mpres_trans H HH _ _ _ MPc13 (ah_mpres_trans H HH _ _ _ MP14 (ah_mpres_trans H HH _ _ _ MP15 MP16))) as MPc16.
    destruct (Z.leb_spec (br_rv res) 0) as [LE0|GT0]; intros VIS16.
    - (* [comment removed for export] *)
      eapply ((DCI adwk_raise) p A nA pbin Bb (mb_len R) bs R' a TB (chainBT H TB a mb2 FB MBL) ff fp n fj24 tpb fj128 fk2 jz jg e5 NAR9 NBR9 MST9 POS9 BTR BTF FRESH9
                [] [] S M [] _ (wz ARP_FILE) x192 x200 x208 x224 x232 _ tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um9 uf m9 s8' msF16 mo16 ARP_FUNC S_ARP_FUNC K_ARP_FUNC AFB_631_R1 AFB_631_R2 AFB_631_R3 631 AR_INTERNAL_ERROR);
        [exact R_ARP_FUNC| discriminate| rewrite S_ARP_FUNC_len; clear; lia| unfold ARP_FUNC; clear; lia| exact DW9| exact VIS16| exact KREL16| exact MPc16| apply BD9; unfold ERRDEBUG_BYTES, DLOOP_BYTES, DLOOP_CNT; clear; lia
        | unfold um9, FMT_UM, lad_cm, DECODE_CUM_BYTES, ERRDEBUG_BYTES, OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - UMB EBR LT9; lia
        | unfold FMT_UF, lad_cf, DECODE_CUM_BYTES, ERRDEBUG_BYTES in *; clear - UFB EBR; lia
        | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
        | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
        | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact He
        | clear; lia| unfold AR_INTERNAL_ERROR; clear; lia
        | unfold AFB_631_R1; clear; lia| reflexivity| unfold AFB_631_R2; clear; lia| reflexivity| unfold AFB_631_R3; clear; lia| reflexivity
        | apply arglue_of_arp; exact afb_631a| apply arglue_of_arp; exact afb_631b|].
      intros u0' u1' u2' b0 b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' msF17 m10 mo17 s10' LEn M'' c XS10 VIS17 KREL17 MP17 DW10 STEP10 ME10 DL10 FXS10 XP10.
      pose proof DW10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI10 & _).
      eapply (ahh_evt_then H HH); [exact KREL17| exact VIS17| eapply afb_seg9; exact MI10|]. intros msF18 mo18 KREL18 MP18 VIS18. cbn beta in VIS18.
      eapply (ERRL p A nA pbin Bb (mb_len R) bs R' a TB (chainBT H TB a mb2 FB MBL) ff fp n fj24 tpb fj128 fk2 jz jg e5 NAR9 NBR9 MST9 POS9 BTR BTF FRESH9
                (btfree_chain p A nA pbin Bb (mb_len R) bs R' a FB MBL mb2 ff fp n fj24 tpb fj128 fk2 jz jg e5 (proj1 NAR9) (proj1 NBR9)) [] S M'' (LEn ++ []));
        [exact DW10| left; reflexivity| unfold dnb; cbn [length Z.of_nat]; change (lb_bytes []) with 0; unfold DECODE_CNT, DECODE_BYTES; clear; lia
        | unfold um9, FMT_UF, lad_cf, DECODE_CUM_BYTES, ERRDEBUG_BYTES in *; clear - UFB EBR; lia
        | unfold um9, FMT_UM, lad_cm, DECODE_CUM_BYTES, ERRDEBUG_BYTES, OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - UMB EBR LT9; lia
        | exact VIS18| exact KREL18| exact (ah_mpres_trans H HH _ _ _ MP17 MP18)].
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 (br_rv res) : word) with (Z_to_bv 64 (zlength bs) : word) in VIS16 by (rewrite ZL; f_equal; clear - RVF GT0; lia).
      eapply (RPFLAT p A nA pbin Bb (mb_len R) bs R' a TB (chainBT H TB a mb2 FB MBL) ff fp n fj24 tpb fj128 fk2 jz jg e5 NAR9 NBR9 MST9 POS9 BTR BTF FRESH9
                (btfree_chain p A nA pbin Bb (mb_len R) bs R' a FB MBL mb2 ff fp n fj24 tpb fj128 fk2 jz jg e5 (proj1 NAR9) (proj1 NBR9)) M []);
        [exact DW9
        | unfold um9, FMT_UM, lad_cm, DECODE_CUM_BYTES, DLOOP_CM, OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - UMB EBR LT9; lia
        | unfold FMT_UF, lad_cf, DECODE_CUM_BYTES, DLOOP_CF in *; clear - UFB EBR; lia
        | apply BD9; apply Z.le_refl
        | exact VIS16| exact KREL16| exact MPc16].
  Qed.
End RC.
