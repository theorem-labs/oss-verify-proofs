(* talk, PLAIN build: the fragment F_attr of lib/Prog/talk_defs.v, the attribute loop of the first
   RTM_NEWLINK, 0x158f4 .. 0x15a6c (exits to 0x1584c with a0 = 0).

     0x158f4  l = lbu 1(b+a) << 8 | lbu 0(b+a) in s4; a0 = 0; l < 4 or al < l -> 0x1584c
     0x15914  t = lbu 3(b+a) << 8 | lbu 2(b+a)
              t = 0x12 (IFLA_LINKINFO): l < 8 -> 0x15a54, else s3 = l-4, s8 = a+4, F_kind at 0x159ac
              t = 0x14 (IFLA_IFALIAS): ld a0, 8(sp) (the alias flag); zero -> 0x15a54, else F_take_al
              other -> 0x15a54
     0x15a54  s4 += 3; a0 = s4 & 0x1fffc (= nl_align l); al -= a0; a += a0; al >= 4 -> 0x158f4,
              else a0 = 0 -> 0x1584c

   The loop is proved by induction on the fuel of attr_scan (ka_all), one turn per step (ka_step):
   ka_head walks 0x158f4 to its four exits, ka_tail walks 0x15a54, and ka_after puts ka_tail and the
   next turn together. attr_scan (S f) calls kind_scan f, so the kind loop gets the fuel f. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit talk_kind.
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
   1. attr_scan, one turn at a time
   -------------------------------------------------------------------------- *)

Lemma ka_scan_lt : forall f c off left acc, left < 4 -> attr_scan f c off left acc = acc.
Proof.
  intros f c off left acc H. destruct f as [|f]; [reflexivity|].
  cbn [attr_scan]. unfold RTA_HDR. destruct (Z.ltb_spec left 4); [reflexivity | lia].
Qed.

Lemma ka_scan_stop : forall f c off left acc, 4 <= left -> (rd16 c off < 4 \/ left < rd16 c off) ->
  attr_scan (S f) c off left acc = acc.
Proof.
  intros f c off left acc H1 H2. cbn [attr_scan]. unfold RTA_HDR.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [reflexivity|].
  destruct (Z.ltb_spec left (rd16 c off)); [reflexivity | lia].
Qed.

Lemma ka_scan_alias : forall f c off left ak aa, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 20 ->
  attr_scan (S f) c off left (Attrs ak aa)
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Attrs ak (Some (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR)))).
Proof.
  intros f c off left ak aa H1 H2 H3. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

Lemma ka_scan_link : forall f c off left ak aa, 4 <= left -> 4 <= rd16 c off <= left -> rd16 c (off + 2) = 18 ->
  attr_scan (S f) c off left (Attrs ak aa)
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (Attrs (kind_scan f c (off + 4) (rd16 c off - 4) ak) aa).
Proof.
  intros f c off left ak aa H1 H2 H3. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite H3. reflexivity.
Qed.

Lemma ka_scan_other : forall f c off left acc, 4 <= left -> 4 <= rd16 c off <= left ->
  rd16 c (off + 2) <> 18 -> rd16 c (off + 2) <> 20 ->
  attr_scan (S f) c off left acc
  = attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off)) acc.
Proof.
  intros f c off left acc H1 H2 H3 H4. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  destruct (Z.ltb_spec left 4); [lia|].
  destruct (Z.ltb_spec (rd16 c off) 4); [lia|].
  destruct (Z.ltb_spec left (rd16 c off)); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.

(* a text once found stays found *)
Lemma ka_scan_kind_some : forall f c off left acc, a_kind acc <> None -> a_kind (attr_scan f c off left acc) <> None.
Proof.
  induction f as [|f IH]; intros c off left acc H; [exact H|]. cbn [attr_scan].
  destruct (left <? RTA_HDR); [exact H|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [exact H|].
  apply IH.
  destruct (rd16 c (off + 2) =? IFLA_IFALIAS); [exact H|].
  destruct (rd16 c (off + 2) =? IFLA_LINKINFO); [|exact H].
  cbn [a_kind]. destruct (a_kind acc) as [x|]; [apply kk_scan_some | exfalso; apply H; reflexivity].
Qed.

Lemma ka_scan_alias_some : forall f c off left acc, a_alias acc <> None -> a_alias (attr_scan f c off left acc) <> None.
Proof.
  induction f as [|f IH]; intros c off left acc H; [exact H|]. cbn [attr_scan].
  destruct (left <? RTA_HDR); [exact H|].
  destruct ((rd16 c off <? RTA_HDR) || (left <? rd16 c off)); [exact H|].
  apply IH.
  destruct (rd16 c (off + 2) =? IFLA_IFALIAS); [cbn [a_alias]; discriminate|].
  destruct (rd16 c (off + 2) =? IFLA_LINKINFO); exact H.
Qed.

Lemma ka_kind_none : forall f c off left acc, a_kind (attr_scan f c off left acc) = None -> a_kind acc = None.
Proof.
  intros f c off left acc H. destruct (a_kind acc) as [x|] eqn:E; [|reflexivity].
  exfalso. apply (ka_scan_kind_some f c off left acc); [rewrite E; discriminate | exact H].
Qed.

Lemma ka_alias_none : forall f c off left acc, a_alias (attr_scan f c off left acc) = None -> a_alias acc = None.
Proof.
  intros f c off left acc H. destruct (a_alias acc) as [x|] eqn:E; [|reflexivity].
  exfalso. apply (ka_scan_alias_some f c off left acc); [rewrite E; discriminate | exact H].
Qed.

(* --------------------------------------------------------------------------
   2. footprints and memory
   -------------------------------------------------------------------------- *)

Lemma ka_w_k : forall X1 n1 X2 n2 m m1, munch [(X1, X1 + n1)] m m1 -> munch [(X1, X1 + n1); (X2, X2 + n2)] m m1.
Proof.
  intros X1 n1 X2 n2 m m1 H. apply (munch_weaken [(X1, X1 + n1)]); [|exact H].
  intros x Hx. cbn [outside] in Hx |- *. tauto.
Qed.

Lemma ka_w_a : forall X1 n1 X2 n2 m m1, munch [(X2, X2 + n2)] m m1 -> munch [(X1, X1 + n1); (X2, X2 + n2)] m m1.
Proof.
  intros X1 n1 X2 n2 m m1 H. apply (munch_weaken [(X2, X2 + n2)]); [|exact H].
  intros x Hx. cbn [outside] in Hx |- *. tauto.
Qed.

Lemma ka_w_0 : forall W m m1, munch [] m m1 -> munch W m m1.
Proof. intros W m m1 H. apply (munch_weaken []); [|exact H]. intros x _. exact I. Qed.

(* a write of width bw: nothing, or the whole live buffer *)
Lemma ka_munch_bw : forall KD KN m m1, 0 <= KN -> munch [(KD, KD + bw KD KN)] m m1 ->
  munch [] m m1 \/ (KD <> 0 /\ 1 <= KN /\ munch [(KD, KD + KN)] m m1).
Proof.
  intros KD KN m m1 HKN MU. destruct (Z.eq_dec KD 0) as [E|E].
  - subst KD. replace (bw 0 KN) with 0 in MU by reflexivity.
    left. intros x _. apply MU. cbn [outside]. split; [lia | exact I].
  - rewrite (kk_bw KD KN E) in MU. destruct (Z.eq_dec KN 0) as [E2|E2].
    + subst KN. left. intros x _. apply MU. cbn [outside]. split; [lia | exact I].
    + right. split; [exact E|]. split; [lia | exact MU].
Qed.

Lemma ka_spill_bw : forall m m1 B n SP KD KN AD AN, 0 <= KN -> bufsep B n SP KD KN AD AN ->
  munch [(KD, KD + bw KD KN)] m m1 -> wmono rsegs m m1 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) -> rw_cells rsegs m1 (SP + -144) (spill_cells AN B KN AD KD).
Proof.
  intros m m1 B n SP KD KN AD AN HKN (SK & _ & _) MU WM H.
  destruct (ka_munch_bw KD KN m m1 HKN MU) as [M0 | (H1 & H2 & MU')].
  - eapply rw_cells_transport; [exact H | exact M0 | exact WM | exact I].
  - destruct (SK H1 H2) as [_ S2]. eapply kk_spill_tr; [exact MU' | exact WM | exact S2 | exact H].
Qed.

Lemma ka_bytes_bw : forall m m1 B ck SP KD KN AD AN, 0 <= KN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  munch [(KD, KD + bw KD KN)] m m1 -> bytes_at rsegs m B ck -> bytes_at rsegs m1 B ck.
Proof.
  intros m m1 B ck SP KD KN AD AN HKN (SK & _ & _) MU H.
  destruct (ka_munch_bw KD KN m m1 HKN MU) as [M0 | (H1 & H2 & MU')].
  - eapply bytes_at_transport; [exact H | exact M0 | exact I].
  - destruct (SK H1 H2) as [S1 _]. eapply kk_bytes_tr; [exact MU' | | exact H]. unfold apart in S1. lia.
Qed.

(* the buffers when the flag of the alias buffer is zero: nothing to say about the alias *)
Lemma ka_bufs_noflag : forall m ak aa x KD KN AD AN, (AD = 0 \/ AN = 0) ->
  bufs m (Attrs ak aa) KD KN AD AN -> bufs m (Attrs ak x) KD KN AD AN.
Proof.
  intros m ak aa x KD KN AD AN HZ (B1 & B2 & B3 & B4).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  intros pay _ H1 H2. exfalso. lia.
Qed.

(* --------------------------------------------------------------------------
   3. the walk
   -------------------------------------------------------------------------- *)

Ltac ka_weq := first [ reflexivity | f_equal; lia ].

(* 0x158f4 .. 0x159a8: the length and type of one attribute, and the alias flag *)
Lemma ka_head : forall (Q : machine_state -> Prop)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (a al SP KD KN AD AN : Z),
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) -> 144 <= SP <= 2 ^ 63 ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= a -> a + al <= Z.of_nat (length ck) -> 4 <= al ->
  ((rd16 ck a < 4 \/ al < rd16 ck a) ->
     forall a1' a2' s4',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 (Z_to_bv 64 4)
                (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 s4' s5 (Z_to_bv 64 B) (Z_to_bv 64 al) s8 s9 s10
                (Z_to_bv 64 a) t3 t4 t5 t6)
           F (Z_to_bv 64 0x1584c) fc None m (seg_rom rsegs))) ->
  (4 <= rd16 ck a <= al ->
     ((rd16 ck (a + 2) = 18 /\ rd16 ck a < 8) \/ (rd16 ck (a + 2) = 20 /\ flagz AD AN = 0) \/
      (rd16 ck (a + 2) <> 18 /\ rd16 ck (a + 2) <> 20)) ->
     forall a0' a1' a2',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4)
                (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 (Z_to_bv 64 (rd16 ck a)) s5 (Z_to_bv 64 B) (Z_to_bv 64 al)
                s8 s9 s10 (Z_to_bv 64 a) t3 t4 t5 t6)
           F (Z_to_bv 64 0x15a54) fc None m (seg_rom rsegs))) ->
  (4 <= rd16 ck a <= al -> rd16 ck (a + 2) = 18 -> 8 <= rd16 ck a ->
     forall a0' a1' a2' s3' s8',
     s3' = Z_to_bv 64 (rd16 ck a - 4) -> s8' = Z_to_bv 64 (a + 4) ->
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4)
                (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3' (Z_to_bv 64 (rd16 ck a)) s5 (Z_to_bv 64 B) (Z_to_bv 64 al)
                s8' s9 s10 (Z_to_bv 64 a) t3 t4 t5 t6)
           F (Z_to_bv 64 0x159ac) fc None m (seg_rom rsegs))) ->
  (4 <= rd16 ck a <= al -> rd16 ck (a + 2) = 20 -> flagz AD AN <> 0 ->
     forall a0' a1' a2',
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 (Z_to_bv 64 4)
                (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 (Z_to_bv 64 (rd16 ck a)) s5 (Z_to_bv 64 B) (Z_to_bv 64 al)
                s8 s9 s10 (Z_to_bv 64 a) t3 t4 t5 t6)
           F (Z_to_bv 64 0x1593c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 4) (Z_to_bv 64 1)
             (Z_to_bv 64 3) a7 s2 s3 s4 s5 (Z_to_bv 64 B) (Z_to_bv 64 al) s8 s9 s10 (Z_to_bv 64 a) t3 t4 t5 t6)
        F (Z_to_bv 64 0x158f4) fc None m (seg_rom rsegs)).
Proof.
  intros until AN. intros SPILL HSP HB HL HB0 HB1 Ha Hal H4 Z1 Zn Zk Za.
  unfold mkR in Z1, Zn, Zk, Za. unfold spill_cells in SPILL.
  destruct (tk_nth_some ck (Z.to_nat a)) as [b0 E0]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (a + 1))) as [b1 E1]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (a + 2))) as [b2 E2]; [lia|].
  destruct (tk_nth_some ck (Z.to_nat (a + 2 + 1))) as [b3 E3]; [lia|].
  pose proof (tk_read1 m B ck a b0 HB Ha E0) as R0.
  pose proof (tk_read1 m B ck (a + 1) b1 HB ltac:(lia) E1) as R1.
  pose proof (tk_read1 m B ck (a + 2) b2 HB ltac:(lia) E2) as R2.
  pose proof (tk_read1 m B ck (a + 2 + 1) b3 HB ltac:(lia) E3) as R3.
  pose proof (kk_rd16_range ck a ltac:(lia) ltac:(lia)) as RL.
  pose proof (kk_rd16_range ck (a + 2) ltac:(lia) ltac:(lia)) as RT.
  pose proof (kk_flag_range AD AN) as RF.
  step. step. step. step. step.
  rewrite (kk_rd16w ck a b0 b1) by first [assumption | lia].
  step. step.
  rewrite (tk_ltu (rd16 ck a) 4) by lia.
  destruct (Z.ltb_spec (rd16 ck a) 4) as [L1|L1]; cbv iota.
  { apply Z1. left. exact L1. }
  step.
  rewrite (tk_ltu al (rd16 ck a)) by lia.
  destruct (Z.ltb_spec al (rd16 ck a)) as [L2|L2]; cbv iota.
  { apply Z1. right. exact L2. }
  step. step. step. step.
  rewrite (kk_rd16w ck (a + 2) b2 b3) by first [assumption | lia].
  step. step.
  rewrite (tk_eqb (rd16 ck (a + 2)) 18) by lia.
  destruct (Z.eqb_spec (rd16 ck (a + 2)) 18) as [T18|T18]; cbv iota.
  - step. step.
    rewrite (tk_ltu (rd16 ck a) 8) by lia.
    destruct (Z.ltb_spec (rd16 ck a) 8) as [L8|L8]; cbv iota.
    + apply Zn; [lia | left; split; assumption].
    + step. step. apply Zk; [lia | exact T18 | lia | ka_weq | ka_weq].
  - step. step.
    rewrite (tk_eqb (rd16 ck (a + 2)) 20) by lia.
    destruct (Z.eqb_spec (rd16 ck (a + 2)) 20) as [T20|T20]; cbn [negb]; cbv iota.
    + step. step.
      rewrite (tk_eqb (flagz AD AN) 0) by lia.
      destruct (Z.eqb_spec (flagz AD AN) 0) as [FZ|FZ]; cbv iota.
      * apply Zn; [lia | right; left; split; assumption].
      * apply Za; [lia | exact T20 | exact FZ].
    + apply Zn; [lia | right; right; split; assumption].
Qed.

(* 0x15a54 .. 0x15a6c: the step to the next attribute, or the end of the loop with a0 = 0 *)
Lemma ka_tail : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s5 s6 s8 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a al l : Z),
  4 <= l <= al -> al <= 4096 -> 0 <= a <= 4096 ->
  (4 <= al - nl_align l -> forall a0' s4' s7' s11',
     s7' = Z_to_bv 64 (al - nl_align l) -> s11' = Z_to_bv 64 (a + nl_align l) ->
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 (Z_to_bv 64 4) a5 a6 a7 s2 s3 s4' s5 s6 s7' s8
                (Z_to_bv 64 0x1fffc) s10 s11' t3 t4 t5 t6)
           F (Z_to_bv 64 0x158f4) fc None m (seg_rom rsegs))) ->
  (al - nl_align l < 4 -> forall s4' s7' s11',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 (Z_to_bv 64 4) a5 a6 a7 s2 s3 s4' s5 s6 s7' s8
                (Z_to_bv 64 0x1fffc) s10 s11' t3 t4 t5 t6)
           F (Z_to_bv 64 0x1584c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 4) a5 a6 a7 s2 s3 (Z_to_bv 64 l) s5 s6
             (Z_to_bv 64 al) s8 (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 a) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a54) fc None m (seg_rom rsegs)).
Proof.
  intros until l. intros H1 H2 H3 W1 W2.
  unfold mkR in W1, W2.
  pose proof (nl_align_le l ltac:(lia)) as NA.
  step. step. step. step. step.
  rewrite (unsigned_lit (l + 3)) by lia.
  rewrite (kk_land_align l) by lia.
  rewrite (unsigned_lit (nl_align l)) by lia.
  rewrite (unsigned_lit al) by lia.
  try rewrite (unsigned_lit a) by lia.
  rewrite (tk_lts (al - nl_align l) 4) by lia.
  destruct (Z.ltb_spec (al - nl_align l) 4) as [L|L]; cbn [negb]; cbv iota.
  - step. step. apply W2. exact L.
  - apply W1; [lia | reflexivity | f_equal; lia].
Qed.

(* F_attr_spec with the fuel fixed (the same statement, fu taken out to the front) *)
Definition ka_P (fu : nat) : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (a al SP KD KN AD AN : Z) (acc : attrs),
  s6 = Z_to_bv 64 B -> s5 = Z_to_bv 64 (B + 4) -> s11 = Z_to_bv 64 a -> s7 = Z_to_bv 64 al ->
  a4 = Z_to_bv 64 4 -> a5 = Z_to_bv 64 1 -> a6 = Z_to_bv 64 3 -> s9 = Z_to_bv 64 0x1fffc ->
  s1 = Z_to_bv 64 KD -> s0 = Z_to_bv 64 AD -> sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= a -> a + al <= Z.of_nat (length ck) -> 4 <= al < Z.of_nat fu ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m acc KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m ->
  (forall m',
     let accF := attr_scan fu ck a al acc in
     munch [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' accF KD KN AD AN ->
     (a_kind accF = None -> munch [(AD, AD + bw AD AN)] m m') ->
     (a_alias accF = None -> munch [(KD, KD + bw KD KN)] m m') ->
     forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s7' s8' s10' s11' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                s2' s3' s4' s5 s6 s7' s8' s9 s10' s11' t3' t4' t5' t6')
           F (Z_to_bv 64 0x1584c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158f4) fc None m (seg_rom rsegs)).

(* from 0x15a54 (memory m1, attributes acc1 after this attribute) through the next turns *)
Lemma ka_after : forall f, ka_P f -> forall (Q : machine_state -> Prop)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a7 s2 s3 s8 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
    (B : Z) (ck : list byte) (a al l SP KD KN AD AN : Z) (acc1 : attrs),
  144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m1 (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m1 B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= a -> a + al <= Z.of_nat (length ck) -> 4 <= l <= al -> al < Z.of_nat (S f) ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m1 acc1 KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m1 ->
  munch [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] m m1 -> wmono rsegs m m1 ->
  (a_kind acc1 = None -> munch [(AD, AD + bw AD AN)] m m1) ->
  (a_alias acc1 = None -> munch [(KD, KD + bw KD KN)] m m1) ->
  (forall m',
     munch [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' (attr_scan f ck (a + nl_align l) (al - nl_align l) acc1) KD KN AD AN ->
     (a_kind (attr_scan f ck (a + nl_align l) (al - nl_align l) acc1) = None ->
        munch [(AD, AD + bw AD AN)] m m') ->
     (a_alias (attr_scan f ck (a + nl_align l) (al - nl_align l) acc1) = None ->
        munch [(KD, KD + bw KD KN)] m m') ->
     forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s7' s8' s10' s11' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' (Z_to_bv 64 (SP + -144)) gp tp t0' t1' t2' (Z_to_bv 64 AD) (Z_to_bv 64 KD) (Z_to_bv 64 0)
                a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B) s7' s8'
                (Z_to_bv 64 0x1fffc) s10' s11' t3' t4' t5' t6')
           F (Z_to_bv 64 0x1584c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0 a1 a2 a3
             (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 (Z_to_bv 64 l) (Z_to_bv 64 (B + 4))
             (Z_to_bv 64 B) (Z_to_bv 64 al) s8 (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 a) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a54) fc None m1 (seg_rom rsegs)).
Proof.
  intros f IH Q ra gp tp t0 t1 t2 a0 a1 a2 a3 a7 s2 s3 s8 s10 t3 t4 t5 t6 F fc m m1 B ck a al l SP KD KN AD AN acc1
    HSP SPILL HB HL HB0 HB1 Ha Hal Hl Hfu HKD HKN HAD HAN BU SEP MI MU WM NK NA K0.
  pose proof (nl_align_le l ltac:(lia)) as NAl.
  apply (ka_tail Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0 a1 a2 a3
           (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B) s8 s10 t3 t4 t5 t6
           F fc m1 a al l); [lia | lia | lia | |].
  - intros HY a0' s4' s7' s11' -> ->.
    unfold ka_P in IH.
    eapply (IH Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0' a1 a2 a3
              (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 s4' (Z_to_bv 64 (B + 4)) (Z_to_bv 64 B)
              (Z_to_bv 64 (al - nl_align l)) s8 (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 (a + nl_align l))
              t3 t4 t5 t6 F fc m1 B ck (a + nl_align l) (al - nl_align l) SP KD KN AD AN acc1); [kk_side .. |].
    intros m'. cbv zeta. intros MU' WM' MI' BU' NK' NA'.
    apply K0; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption | exact MI' | exact BU' | |].
    + intros HN. eapply munch_trans; [apply NK; exact (ka_kind_none _ _ _ _ _ HN) | apply NK'; exact HN].
    + intros HN. eapply munch_trans; [apply NA; exact (ka_alias_none _ _ _ _ _ HN) | apply NA'; exact HN].
  - intros HY s4' s7' s11'.
    rewrite (ka_scan_lt f ck (a + nl_align l) (al - nl_align l) acc1) in K0 by lia.
    apply K0; [exact MU | exact WM | exact MI | exact BU | exact NK | exact NA].
Qed.

(* one turn of the loop *)
Lemma ka_step : F_take_al_spec -> F_kind_spec -> forall f, ka_P f -> ka_P (S f).
Proof.
  intros TA TKs f IH. unfold ka_P.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck a al SP KD KN AD AN [ak aa] -> -> -> -> -> -> -> -> -> -> ->
    HSP SPILL HB HL HB0 HB1 Ha Hal Hfu HKD HKN HAD HAN BUFS SEP MI K.
  cbv zeta in K.
  apply (ka_head Q ra gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0 a1 a2 a3 a7 s2 s3 s4 (Z_to_bv 64 (B + 4))
           s8 (Z_to_bv 64 0x1fffc) s10 t3 t4 t5 t6 F fc m B ck a al SP KD KN AD AN); try assumption; try lia.
  - (* l < 4 or al < l: the loop ends with a0 = 0 *)
    intros HX a1' a2' s4'.
    rewrite (ka_scan_stop f ck a al (Attrs ak aa)) in K by lia.
    apply K; [apply munch_refl | apply wmono_refl | exact MI | exact BUFS | intros _; apply munch_refl
             | intros _; apply munch_refl].
  - (* no write *)
    intros HX HT a0' a1' a2'.
    destruct HT as [[T18 L8] | [[T20 FZ] | [N18 N20]]].
    + (* IFLA_LINKINFO too short to hold an attribute *)
      rewrite (ka_scan_link f ck a al ak aa) in K by lia.
      rewrite (kk_scan_lt f ck (a + 4) (rd16 ck a - 4) ak) in K by lia.
      apply (ka_after f IH Q ra gp tp t0 t1 t2 a0' a1' a2' a3 a7 s2 s3 s8 s10 t3 t4 t5 t6 F fc m m B ck a al
               (rd16 ck a) SP KD KN AD AN (Attrs ak aa));
        try solve [kk_side | apply munch_refl | apply wmono_refl | intros _; apply munch_refl].
    + (* IFLA_IFALIAS with a zero flag *)
      rewrite (ka_scan_alias f ck a al ak aa) in K by lia.
      apply (ka_after f IH Q ra gp tp t0 t1 t2 a0' a1' a2' a3 a7 s2 s3 s8 s10 t3 t4 t5 t6 F fc m m B ck a al
               (rd16 ck a) SP KD KN AD AN (Attrs ak (Some (slice ck (a + RTA_HDR) (rd16 ck a - RTA_HDR)))));
        try solve [kk_side | apply munch_refl | apply wmono_refl | intros _; apply munch_refl].
      apply (ka_bufs_noflag m ak aa); [apply kk_flag_z; exact FZ | exact BUFS].
    + (* another type *)
      rewrite (ka_scan_other f ck a al (Attrs ak aa)) in K by lia.
      apply (ka_after f IH Q ra gp tp t0 t1 t2 a0' a1' a2' a3 a7 s2 s3 s8 s10 t3 t4 t5 t6 F fc m m B ck a al
               (rd16 ck a) SP KD KN AD AN (Attrs ak aa));
        try solve [kk_side | apply munch_refl | apply wmono_refl | intros _; apply munch_refl].
  - (* IFLA_LINKINFO: the kind loop with the fuel f *)
    intros HX HT H8 a0' a1' a2' s3' s8' E3 E8.
    rewrite (ka_scan_link f ck a al ak aa) in K by lia.
    eapply (TKs Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0' a1' a2' a3
              (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3' (Z_to_bv 64 (rd16 ck a)) (Z_to_bv 64 (B + 4))
              (Z_to_bv 64 B) (Z_to_bv 64 al) s8' (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 a) t3 t4 t5 t6 F fc m
              B ck f (a + 4) (rd16 ck a - 4) SP KD KN AD AN (Attrs ak aa)); [kk_side .. |].
    intros m1. cbv zeta. cbn [a_kind a_alias]. intros MU1 WM1 MI1 BU1 NN1.
    intros ra' t0' t1' t2' a0'' a1'' a2'' a3' a7' s2' s3'' s8'' s10' t3' t4' t5' t6'.
    apply (ka_after f IH Q ra' gp tp t0' t1' t2' a0'' a1'' a2'' a3' a7' s2' s3'' s8'' s10' t3' t4' t5' t6' F fc
             m m1 B ck a al (rd16 ck a) SP KD KN AD AN (Attrs (kind_scan f ck (a + 4) (rd16 ck a - 4) ak) aa));
      try solve [kk_side].
    + eapply ka_spill_bw; [ | exact SEP | exact MU1 | exact WM1 | exact SPILL]. lia.
    + eapply ka_bytes_bw; [ | exact SEP | exact MU1 | exact HB]. lia.
    + apply ka_w_k. exact MU1.
    + intros HN. apply ka_w_0. apply NN1. exact HN.
    + intros _. exact MU1.
  - (* IFLA_IFALIAS with a non-zero flag: take_text into the alias buffer *)
    intros HX HT HF a0' a1' a2'.
    destruct (kk_flag_nz AD AN HF ltac:(lia)) as [HA0 HA1].
    destruct (proj1 (proj2 BUFS) HA0 HA1) as [jk RWA].
    pose proof SEP as (_ & SA & _). destruct (SA HA0 HA1) as [SAB SAS].
    rewrite (ka_scan_alias f ck a al ak aa) in K by lia.
    eapply (TA Q ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0' a1' a2' a3
              (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3) a7 s2 s3 (Z_to_bv 64 (rd16 ck a)) (Z_to_bv 64 (B + 4))
              (Z_to_bv 64 B) (Z_to_bv 64 al) s8 (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 a) t3 t4 t5 t6 F fc m
              B ck a (rd16 ck a) SP KD KN AD AN jk); [kk_side .. |].
    intros m1 MU1 WM1 MI1 CS1 RW1 ra' t0' t1' t2' a0'' a1'' a2'' a3' a7' s2' t3' t4' t5' t6'.
    apply (ka_after f IH Q ra' gp tp t0' t1' t2' a0'' a1'' a2'' a3' a7' s2' s3 s8 s10 t3' t4' t5' t6' F fc
             m m1 B ck a al (rd16 ck a) SP KD KN AD AN
             (Attrs ak (Some (slice ck (a + RTA_HDR) (rd16 ck a - RTA_HDR)))));
      try solve [kk_side].
    + eapply kk_spill_tr; [exact MU1 | exact WM1 | exact SAS | exact SPILL].
    + eapply kk_bytes_tr; [exact MU1 | | exact HB]. unfold apart in SAB. lia.
    + eapply kk_bufs_alias; eassumption.
    + apply ka_w_a. rewrite (kk_bw AD AN HA0). exact MU1.
    + intros _. rewrite (kk_bw AD AN HA0). exact MU1.
    + intros E. discriminate E.
Qed.

Lemma ka_all : F_take_al_spec -> F_kind_spec -> forall fu, ka_P fu.
Proof.
  intros TA TKs fu. induction fu as [|f IH].
  - unfold ka_P. intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m B ck a al SP KD KN AD AN acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfu.
    exfalso. cbn in Hfu. lia.
  - apply ka_step; assumption.
Qed.

Lemma F_attr_ok : F_take_al_spec -> F_kind_spec -> F_attr_spec.
Proof.
  intros TA TKs. unfold F_attr_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck fu.
  exact (ka_all TA TKs fu Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m B ck).
Qed.

Print Assumptions F_attr_ok.
