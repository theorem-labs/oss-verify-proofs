(* talk, PLAIN build: the fragment F_kind of lib/Prog/talk_defs.v, the loop over the attributes
   inside one IFLA_LINKINFO, 0x159ac .. 0x15a50 (exits to 0x15a54).

     0x159ac  li = lbu 1(b+i) << 8 | lbu 0(b+i) in s10; li < 4 or il < li -> 0x15a54
     0x159c8  ti = lbu 3(b+i) << 8 | lbu 2(b+i); ti <> 1 -> 0x15a40
     0x159dc  ld a0, 0x20(sp) (the kind flag); zero -> 0x15a40
     0x159e4  take_text of the IFLA_INFO_KIND (the fragment F_take_kd), back at 0x15a40
     0x15a40  s10 += 3; a0 = s10 & 0x1fffc (= nl_align li); il -= a0; i += a0; 3 < il -> 0x159ac

   The loop is proved by induction on the fuel of kind_scan (kk_all), one turn per step (kk_step):
   kk_head walks 0x159ac to its three exits, kk_tail walks 0x15a40, and kk_after puts kk_tail and
   the next turn together. The shared helpers (prefix kk_) are used by talk_attr.v too. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Dieta54.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Dieta54.dlia.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------
   1. words and byte lists
   -------------------------------------------------------------------------- *)

(* `(x + 3) & 0x1fffc` is NL_ALIGN(x) for a 16-bit x *)
Lemma kk_land_align : forall x, 0 <= x < 2 ^ 16 -> Z.land (x + 3) 131068 = nl_align x.
Proof.
  intros x Hx. unfold nl_align.
  change 131068 with (Z.ldiff (Z.ones 17) (Z.ones 2)).
  assert (E : Z.land (x + 3) (Z.ldiff (Z.ones 17) (Z.ones 2))
              = Z.ldiff (Z.land (x + 3) (Z.ones 17)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit (x + 3) n), (Z.testbit (Z.ones 17) n), (Z.testbit (Z.ones 2) n); reflexivity. }
  rewrite E. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 2) with 4. lia.
Qed.

(* two bytes joined by lbu, lbu, slli 8, or *)
Lemma kk_rd16w : forall c off (b0 b1 : byte), 0 <= off -> off + 2 <= Z.of_nat (length c) ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0)))
  = Z_to_bv 64 (rd16 c off).
Proof.
  intros c off b0 b1 H1 H2 E0 E1. pose proof (tk_byte_range b0) as R0. pose proof (tk_byte_range b1) as R1.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b1)) by lia. rewrite (unsigned_lit (bv_unsigned b0)) by lia.
  assert (S : Z.shiftl (bv_unsigned b1) 8 = bv_unsigned b1 * 256)
    by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned b1) 8)) by (rewrite S; lia).
  rewrite tk_lor_shl8 by lia. rewrite (tk_rd16 c off b0 b1 H1 H2 E0 E1). reflexivity.
Qed.

Lemma kk_rd16_range : forall c off, 0 <= off -> off + 2 <= Z.of_nat (length c) -> 0 <= rd16 c off < 2 ^ 16.
Proof.
  intros c off H1 H2. unfold rd16. split; [apply tk_rdn_range|].
  pose proof (tk_rdn_bound c off 2 H1 ltac:(lia) H2) as Hb. change (2 ^ (8 * 2)) with (2 ^ 16) in Hb. exact Hb.
Qed.

Lemma kk_flag_range : forall p n, 0 <= flagz p n < 2 ^ 64.
Proof. intros p n. unfold flagz. destruct ((p =? 0) || (n =? 0)); lia. Qed.

Lemma kk_flag_nz : forall p n, flagz p n <> 0 -> 0 <= n -> p <> 0 /\ 1 <= n.
Proof.
  intros p n H Hn. unfold flagz in H.
  destruct (Z.eqb_spec p 0); destruct (Z.eqb_spec n 0); cbn [orb] in H; lia.
Qed.

Lemma kk_flag_z : forall p n, flagz p n = 0 -> p = 0 \/ n = 0.
Proof.
  intros p n H. unfold flagz in H.
  destruct (Z.eqb_spec p 0); destruct (Z.eqb_spec n 0); cbn [orb] in H; lia.
Qed.

Lemma kk_bw : forall p n, p <> 0 -> bw p n = n.
Proof. intros p n H. unfold bw. destruct (Z.eqb_spec p 0); [contradiction | reflexivity]. Qed.

Lemma kk_cut_len : forall pay cap, 1 <= cap -> Z.of_nat (length (cut_text pay cap)) + 1 <= cap.
Proof. intros pay cap H. unfold cut_text. rewrite length_firstn. lia. Qed.

Lemma kk_spill_size : forall AN B KN AD KD, Z.of_nat (cells_size (spill_cells AN B KN AD KD)) = 40.
Proof. intros. reflexivity. Qed.

(* --------------------------------------------------------------------------
   2. kind_scan, one turn at a time
   -------------------------------------------------------------------------- *)

Lemma kk_scan_lt : forall f c off left k, left < 4 -> kind_scan f c off left k = k.
Proof.
  intros f c off left k H. destruct f as [|f]; [reflexivity|].
  cbn [kind_scan]. unfold RTA_HDR. destruct (Z.ltb_spec left 4); [reflexivity | lia].
Qed.

Lemma kk_scan_stop : forall f c off left k, 4 <= left -> (rd16 c off < 4 \/ left < rd16 c off) ->
  kind_scan (S f) c off left k = k.
Proof.
  intros f c off left k H1 H2. cbn [kind_scan]. unfold RTA_HDR.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [reflexivity|].
  destruct (Z.ltb_spec left (rd16 c off)); [reflexivity | lia].
Qed.

Lemma kk_scan_kind : forall f c off left k, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 1 ->
  kind_scan (S f) c off left k
  = kind_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Some (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR))).
Proof.
  intros f c off left k H1 H2 H3. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

Lemma kk_scan_other : forall f c off left k, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) <> 1 ->
  kind_scan (S f) c off left k
  = kind_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off)) k.
Proof.
  intros f c off left k H1 H2 H3. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.

(* the kind once found stays found *)
Lemma kk_scan_some : forall f c off left x, kind_scan f c off left (Some x) <> None.
Proof.
  induction f as [|f IH]; intros c off left x; [discriminate|].
  cbn [kind_scan].
  destruct (left <? RTA_HDR); [discriminate|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [discriminate|].
  destruct (rd16 c (off + 2) =? INFO_KIND); apply IH.
Qed.

(* --------------------------------------------------------------------------
   3. memory across a write to one buffer
   -------------------------------------------------------------------------- *)

Lemma kk_rw_tr : forall X n m m1 A cs, munch [(X, X + n)] m m1 -> wmono rsegs m m1 ->
  (X + n <= A \/ A + Z.of_nat (cells_size cs) <= X) -> rw_cells rsegs m A cs -> rw_cells rsegs m1 A cs.
Proof.
  intros X n m m1 A cs MU WM D H. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma kk_bytes_tr : forall X n m m1 A bs, munch [(X, X + n)] m m1 ->
  (X + n <= A \/ A + Z.of_nat (length bs) <= X) -> bytes_at rsegs m A bs -> bytes_at rsegs m1 A bs.
Proof.
  intros X n m m1 A bs MU D H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma kk_cstr_tr : forall X n m m1 A s, munch [(X, X + n)] m m1 ->
  (X + n <= A \/ A + Z.of_nat (length s) + 1 <= X) -> cstr_at m A s -> cstr_at m1 A s.
Proof.
  intros X n m m1 A s MU D [H N]. split; [|exact N].
  eapply bytes_at_transport; [exact H | exact MU |].
  rewrite length_app. cbn [length disjoint_from]. split; [lia | exact I].
Qed.

Lemma kk_spill_tr : forall X n m m1 SP AN B KN AD KD, munch [(X, X + n)] m m1 -> wmono rsegs m m1 ->
  apart X n (SP + -144) 144 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) -> rw_cells rsegs m1 (SP + -144) (spill_cells AN B KN AD KD).
Proof.
  intros X n m m1 SP AN B KN AD KD MU WM D H. eapply kk_rw_tr; [exact MU | exact WM | | exact H].
  rewrite kk_spill_size. unfold apart in D. lia.
Qed.

(* the buffers when the flag of the kind buffer is zero: nothing to say about the kind *)
Lemma kk_bufs_noflag : forall m k ak aa KD KN AD AN, (KD = 0 \/ KN = 0) ->
  bufs m (Attrs ak aa) KD KN AD AN -> bufs m (Attrs k aa) KD KN AD AN.
Proof.
  intros m k ak aa KD KN AD AN HZ (B1 & B2 & B3 & B4).
  split; [exact B1|]. split; [exact B2|]. split; [|exact B4].
  intros pay _ H1 H2. exfalso. lia.
Qed.

(* the buffers after take_text wrote the kind buffer *)
Lemma kk_bufs_kind : forall m m1 ak aa pay B n SP KD KN AD AN,
  bufs m (Attrs ak aa) KD KN AD AN -> bufsep B n SP KD KN AD AN -> KD <> 0 -> 1 <= KN ->
  munch [(KD, KD + KN)] m m1 -> wmono rsegs m m1 ->
  cstr_at m1 KD (cut_text pay KN) -> (exists j, rw_cells rsegs m1 KD [CB (Z.to_nat KN) j]) ->
  bufs m1 (Attrs (Some pay) aa) KD KN AD AN.
Proof.
  intros m m1 ak aa pay B n SP KD KN AD AN (B1 & B2 & B3 & B4) (S1 & S2 & S3) HKD HKN MU WM CS RW.
  split; [intros _ _; exact RW|]. split.
  - intros HAD HAN. destruct (B2 HAD HAN) as [j Hj]. exists j.
    specialize (S3 HKD HKN HAD HAN). unfold apart in S3.
    eapply kk_rw_tr; [exact MU | exact WM | | exact Hj]. cbn [cells_size csize]. lia.
  - split.
    + intros p E _ _. cbn [a_kind] in E. injection E as <-. exact CS.
    + intros p E HAD HAN. cbn [a_alias] in E.
      specialize (S3 HKD HKN HAD HAN). unfold apart in S3. pose proof (kk_cut_len p AN HAN) as CL.
      eapply kk_cstr_tr; [exact MU | | exact (B4 p E HAD HAN)]. lia.
Qed.

(* the buffers after take_text wrote the alias buffer *)
Lemma kk_bufs_alias : forall m m1 ak aa pay B n SP KD KN AD AN,
  bufs m (Attrs ak aa) KD KN AD AN -> bufsep B n SP KD KN AD AN -> AD <> 0 -> 1 <= AN ->
  munch [(AD, AD + AN)] m m1 -> wmono rsegs m m1 ->
  cstr_at m1 AD (cut_text pay AN) -> (exists j, rw_cells rsegs m1 AD [CB (Z.to_nat AN) j]) ->
  bufs m1 (Attrs ak (Some pay)) KD KN AD AN.
Proof.
  intros m m1 ak aa pay B n SP KD KN AD AN (B1 & B2 & B3 & B4) (S1 & S2 & S3) HAD HAN MU WM CS RW.
  split.
  - intros HKD HKN. destruct (B1 HKD HKN) as [j Hj]. exists j.
    specialize (S3 HKD HKN HAD HAN). unfold apart in S3.
    eapply kk_rw_tr; [exact MU | exact WM | | exact Hj]. cbn [cells_size csize]. lia.
  - split; [intros _ _; exact RW|]. split.
    + intros p E HKD HKN. cbn [a_kind] in E.
      specialize (S3 HKD HKN HAD HAN). unfold apart in S3. pose proof (kk_cut_len p KN HKN) as CL.
      eapply kk_cstr_tr; [exact MU | | exact (B3 p E HKD HKN)]. lia.
    + intros p E _ _. cbn [a_alias] in E. injection E as <-. exact CS.
Qed.

(* --------------------------------------------------------------------------
   4. the walk
   -------------------------------------------------------------------------- *)

(* 0x159ac .. 0x159e0: the length and type of one IFLA_INFO_* and the kind flag *)
Lemma kk_head : forall (Q : machine_state -> Prop)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (i il SP KD KN AD AN : Z),
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) -> 144 <= SP <= 2 ^ 63 ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= i -> i + il <= Z.of_nat (length ck) -> 4 <= il ->
  ((rd16 ck i < 4 \/ il < rd16 ck i) ->
     forall a0' a1' a2' s10',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 s5 (Z_to_bv 64 B) s7 (Z_to_bv 64 i) s9 s10' s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15a54) fc None m (seg_rom rsegs))) ->
  (4 <= rd16 ck i <= il -> (rd16 ck (i + 2) <> 1 \/ flagz KD KN = 0) ->
     forall a0' a1' a2',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 s5 (Z_to_bv 64 B) s7 (Z_to_bv 64 i) s9
                (Z_to_bv 64 (rd16 ck i)) s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15a40) fc None m (seg_rom rsegs))) ->
  (4 <= rd16 ck i <= il -> rd16 ck (i + 2) = 1 -> flagz KD KN <> 0 ->
     forall a0' a1' a2',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 s5 (Z_to_bv 64 B) s7 (Z_to_bv 64 i) s9
                (Z_to_bv 64 (rd16 ck i)) s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x159e4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 4) (Z_to_bv 64 1)
             (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 s5 (Z_to_bv 64 B) s7 (Z_to_bv 64 i) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159ac) fc None m (seg_rom rsegs)).
Proof.
  intros until AN. intros SPILL HSP HB HL HB0 HB1 Hi Hil H4 X1 X2 X3.
  unfold mkR in X1, X2, X3. unfold spill_cells in SPILL.
  destruct (tk_nth_some ck (Z.to_nat i)) as [b0 E0]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (i + 1))) as [b1 E1]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (i + 2))) as [b2 E2]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (i + 2 + 1))) as [b3 E3]; [lia|].
  pose proof (tk_read1 m B ck i b0 HB Hi E0) as R0.
  pose proof (tk_read1 m B ck (i + 1) b1 HB ltac:(lia) E1) as R1.
  pose proof (tk_read1 m B ck (i + 2) b2 HB ltac:(lia) E2) as R2.
  pose proof (tk_read1 m B ck (i + 2 + 1) b3 HB ltac:(lia) E3) as R3.
  pose proof (kk_rd16_range ck i ltac:(lia) ltac:(lia)) as RL.
  pose proof (kk_rd16_range ck (i + 2) ltac:(lia) ltac:(lia)) as RT.
  pose proof (kk_flag_range KD KN) as RF.
  step. step. step. step. step.
  rewrite (kk_rd16w ck i b0 b1) by first [assumption | lia].
  step.
  rewrite (tk_ltu (rd16 ck i) 4) by lia.
  destruct (Z.ltb_spec (rd16 ck i) 4) as [L1|L1]; cbv iota.
  { apply X1. left. exact L1. }
  step.
  rewrite (tk_ltu il (rd16 ck i)) by lia.
  destruct (Z.ltb_spec il (rd16 ck i)) as [L2|L2]; cbv iota.
  { apply X1. right. exact L2. }
  step. step. step. step.
  rewrite (kk_rd16w ck (i + 2) b2 b3) by first [assumption | lia].
  step.
  rewrite (tk_eqb (rd16 ck (i + 2)) 1) by lia.
  destruct (Z.eqb_spec (rd16 ck (i + 2)) 1) as [T|T]; cbn [negb]; cbv iota.
  2:{ apply X2; [lia | left; exact T]. }
  step. step.
  rewrite (tk_eqb (flagz KD KN) 0) by lia.
  destruct (Z.eqb_spec (flagz KD KN) 0) as [Z0|Z0]; cbv iota.
  - apply X2; [lia | right; exact Z0].
  - apply X3; [lia | exact T | exact Z0].
Qed.

(* 0x15a40 .. 0x15a50: the step to the next IFLA_INFO_* *)
Lemma kk_tail : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i il li : Z),
  4 <= li <= il -> il <= 4096 -> 0 <= i <= 4096 ->
  (4 <= il - nl_align li -> forall a0' s3' s8' s10',
     s3' = Z_to_bv 64 (il - nl_align li) -> s8' = Z_to_bv 64 (i + nl_align li) ->
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2
                s3' s4 s5 s6 s7 s8' (Z_to_bv 64 0x1fffc) s10' s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x159ac) fc None m (seg_rom rsegs))) ->
  (il - nl_align li < 4 -> forall a0' s3' s8' s10',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2
                s3' s4 s5 s6 s7 s8' (Z_to_bv 64 0x1fffc) s10' s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15a54) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2
             (Z_to_bv 64 il) s4 s5 s6 s7 (Z_to_bv 64 i) (Z_to_bv 64 0x1fffc) (Z_to_bv 64 li) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a40) fc None m (seg_rom rsegs)).
Proof.
  intros until li. intros H1 H2 H3 Y1 Y2.
  unfold mkR in Y1, Y2.
  pose proof (nl_align_le li ltac:(lia)) as NA.
  step. step. step. step. step.
  rewrite (unsigned_lit (li + 3)) by lia.
  rewrite (kk_land_align li) by lia.
  rewrite (unsigned_lit (nl_align li)) by lia.
  rewrite (unsigned_lit il) by lia.
  rewrite (tk_lts 3 (il - nl_align li)) by lia.
  destruct (Z.ltb_spec 3 (il - nl_align li)) as [L|L]; cbv iota.
  - apply Y1; [lia | reflexivity | f_equal; lia].
  - apply Y2. lia.
Qed.

(* F_kind_spec with the fuel fixed (the same statement, fu taken out to the front) *)
Definition kk_P (fu : nat) : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (i il SP KD KN AD AN : Z) (acc : attrs),
  s6 = Z_to_bv 64 B -> s5 = Z_to_bv 64 (B + 4) -> s8 = Z_to_bv 64 i -> s3 = Z_to_bv 64 il ->
  a4 = Z_to_bv 64 4 -> a5 = Z_to_bv 64 1 -> a6 = Z_to_bv 64 3 -> s9 = Z_to_bv 64 0x1fffc ->
  s1 = Z_to_bv 64 KD -> sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= i -> i + il <= Z.of_nat (length ck) -> 4 <= il < Z.of_nat fu ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m acc KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m ->
  (forall m',
     let acc' := Attrs (kind_scan fu ck i il (a_kind acc)) (a_alias acc) in
     munch [(KD, KD + bw KD KN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' acc' KD KN AD AN ->
     (a_kind acc' = None -> munch [] m m') ->
     forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' s3' s8' s10' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7' s2' s3' s4 s5 s6 s7 s8' s9 s10' s11 t3' t4' t5' t6')
           F (Z_to_bv 64 0x15a54) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159ac) fc None m (seg_rom rsegs)).

Ltac kk_side := first [ reflexivity | eassumption | lia ].

(* from 0x15a40 (memory m1, kind accumulator k') through the next turns, with the fuel f left *)
Lemma kk_after : forall f, kk_P f -> forall (Q : machine_state -> Prop)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a7 s2 s4 s7 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
    (B : Z) (ck : list byte) (i il li SP KD KN AD AN : Z) (k' aa : option (list byte)),
  144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m1 (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m1 B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= i -> i + il <= Z.of_nat (length ck) -> 4 <= li <= il -> il < Z.of_nat (S f) ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m1 (Attrs k' aa) KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m1 ->
  munch [(KD, KD + bw KD KN)] m m1 -> wmono rsegs m m1 -> (k' = None -> munch [] m m1) ->
  (forall m',
     munch [(KD, KD + bw KD KN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' (Attrs (kind_scan f ck (i + nl_align li) (il - nl_align li) k') aa) KD KN AD AN ->
     (kind_scan f ck (i + nl_align li) (il - nl_align li) k' = None -> munch [] m m') ->
     forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' s3' s8' s10' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' (Z_to_bv 64 (SP + -144)) gp tp t0' t1' t2' s0 (Z_to_bv 64 KD) a0' a1' a2' a3'
                (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7' s2' s3' s4 (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B)
                s7 s8' (Z_to_bv 64 0x1fffc) s10' s11 t3' t4' t5' t6')
           F (Z_to_bv 64 0x15a54) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0 a1 a2 a3 (Z_to_bv 64 4)
             (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B) s7
             (Z_to_bv 64 i) (Z_to_bv 64 0x1fffc) (Z_to_bv 64 li) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a40) fc None m1 (seg_rom rsegs)).
Proof.
  intros f IH Q ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a7 s2 s4 s7 s11 t3 t4 t5 t6 F fc m m1 B ck i il li SP KD KN AD AN k' aa
    HSP SPILL HB HL HB0 HB1 Hi Hil Hli Hfu HKD HKN HAD HAN BU SEP MI MU WM NN K0.
  pose proof (nl_align_le li ltac:(lia)) as NA.
  apply (kk_tail Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0 a1 a2 a3 a7 s2 s4
           (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B) s7 s11 t3 t4 t5 t6 F fc m1 i il li); [lia | lia | lia | |].
  - intros HY a0' s3' s8' s10' -> ->.
    unfold kk_P in IH.
    eapply (IH Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0' a1 a2 a3 (Z_to_bv 64 4)
              (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 (il - nl_align li)) s4 (Z_to_bv 64 (B + 4))
              (Z_to_bv 64 B) s7 (Z_to_bv 64 (i + nl_align li)) (Z_to_bv 64 0x1fffc) s10' s11 t3 t4 t5 t6 F fc m1
              B ck (i + nl_align li) (il - nl_align li) SP KD KN AD AN (Attrs k' aa)); [kk_side .. |].
    intros m'. cbv zeta. cbn [a_kind a_alias]. intros MU' WM' MI' BU' NN'.
    apply K0; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption | exact MI' | exact BU' |].
    intros HN. destruct k' as [x|]; [exfalso; exact (kk_scan_some _ _ _ _ x HN) |].
    eapply munch_trans; [apply NN; reflexivity | apply NN'; exact HN].
  - intros HY a0' s3' s8' s10'.
    rewrite (kk_scan_lt f ck (i + nl_align li) (il - nl_align li) k') in K0 by lia.
    apply K0; [exact MU | exact WM | exact MI | exact BU | exact NN].
Qed.

(* one turn of the loop *)
Lemma kk_step : F_take_kd_spec -> forall f, kk_P f -> kk_P (S f).
Proof.
  intros TK f IH. unfold kk_P.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck i il SP KD KN AD AN [ak aa] -> -> -> -> -> -> -> -> -> ->
    HSP SPILL HB HL HB0 HB1 Hi Hil Hfu HKD HKN HAD HAN BUFS SEP MI K.
  cbv zeta in K. cbn [a_kind a_alias] in K.
  pose proof (kk_rd16_range ck i ltac:(lia) ltac:(lia)) as RL.
  apply (kk_head Q ra gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0 a1 a2 a3 a7 s2 s4 (Z_to_bv 64 (B + 4)) s7
           (Z_to_bv 64 0x1fffc) s10 s11 t3 t4 t5 t6 F fc m B ck i il SP KD KN AD AN); try assumption; try lia.
  - (* li < 4 or il < li: the loop ends *)
    intros HX a0' a1' a2' s10'.
    rewrite (kk_scan_stop f ck i il ak) in K by lia.
    apply K; [apply munch_refl | apply wmono_refl | exact MI | exact BUFS | intros _; apply munch_refl].
  - (* no write: another type, or the kind with a zero flag *)
    intros HX HT a0' a1' a2'.
    destruct (Z.eq_dec (rd16 ck (i + 2)) 1) as [T1|T1].
    + destruct HT as [HT|HT]; [contradiction|].
      rewrite (kk_scan_kind f ck i il ak) in K by lia.
      apply (kk_after f IH Q ra gp tp t0 t1 t2 s0 a0' a1' a2' a3 a7 s2 s4 s7 s11 t3 t4 t5 t6 F fc m m B ck i il
               (rd16 ck i) SP KD KN AD AN (Some (slice ck (i + RTA_HDR) (rd16 ck i - RTA_HDR))) aa);
        try solve [kk_side | apply munch_refl | apply wmono_refl].
      * apply (kk_bufs_noflag m _ ak aa); [apply kk_flag_z; exact HT | exact BUFS].
      * intros E. discriminate E.
    + rewrite (kk_scan_other f ck i il ak) in K by lia.
      apply (kk_after f IH Q ra gp tp t0 t1 t2 s0 a0' a1' a2' a3 a7 s2 s4 s7 s11 t3 t4 t5 t6 F fc m m B ck i il
               (rd16 ck i) SP KD KN AD AN ak aa);
        try solve [kk_side | apply munch_refl | apply wmono_refl | intros _; apply munch_refl].
  - (* the kind with a non-zero flag: take_text into the kind buffer *)
    intros HX HT HF a0' a1' a2'.
    destruct (kk_flag_nz KD KN HF ltac:(lia)) as [HK0 HK1].
    destruct (proj1 BUFS HK0 HK1) as [jk RWK].
    pose proof SEP as (SK & _ & _). destruct (SK HK0 HK1) as [SKB SKS].
    rewrite (kk_scan_kind f ck i il ak) in K by lia.
    eapply (TK Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0' a1' a2' a3 (Z_to_bv 64 4)
              (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 (Z_to_bv 64 il) s4 (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B) s7
              (Z_to_bv 64 i) (Z_to_bv 64 0x1fffc) (Z_to_bv 64 (rd16 ck i)) s11 t3 t4 t5 t6 F fc m
              B ck i (rd16 ck i) SP KD KN AD AN jk); [kk_side .. |].
    intros m1 MU1 WM1 MI1 CS1 RW1 ra' t0' t1' t2' a0'' a1'' a2'' a3' a7' s2' t3' t4' t5' t6'.
    apply (kk_after f IH Q ra' gp tp t0' t1' t2' s0 a0'' a1'' a2'' a3' a7' s2' s4 s7 s11 t3' t4' t5' t6' F fc m m1
             B ck i il (rd16 ck i) SP KD KN AD AN (Some (slice ck (i + RTA_HDR) (rd16 ck i - RTA_HDR))) aa);
      try solve [kk_side].
    + eapply kk_spill_tr; [exact MU1 | exact WM1 | exact SKS | exact SPILL].
    + eapply kk_bytes_tr; [exact MU1 | | exact HB]. unfold apart in SKB. lia.
    + eapply kk_bufs_kind; eassumption.
    + rewrite (kk_bw KD KN HK0). exact MU1.
    + intros E. discriminate E.
Qed.

Lemma kk_all : F_take_kd_spec -> forall fu, kk_P fu.
Proof.
  intros TK fu. induction fu as [|f IH].
  - unfold kk_P. intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m B ck i il SP KD KN AD AN acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfu.
    exfalso. cbn in Hfu. lia.
  - apply kk_step; assumption.
Qed.

Lemma F_kind_ok : F_take_kd_spec -> F_kind_spec.
Proof.
  intros TK. unfold F_kind_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck fu.
  exact (kk_all TK fu Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m B ck).
Qed.

Print Assumptions F_kind_ok.
