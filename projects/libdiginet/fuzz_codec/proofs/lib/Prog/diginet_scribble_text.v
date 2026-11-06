From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells memset_c diginet_scribble_text_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import diginet_scribble_text_lem.
Import ListNotations.
Open Scope Z_scope.

(** ---- bytes and the image's code forms ---- *)

Lemma b8_byte : forall b : byte, b8 (bv_unsigned b) = b.
Proof. intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma lts_shl56_check :
  codec_text.all_from (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x)) 0 256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma digit_check :
  codec_text.all_from (fun y => Bool.eqb
    (bv_ltu (Z_to_bv 64 8) (Z_to_bv 64 (Z.land ((y + -49) mod 18446744073709551616) 255)))
    (negb ((49 <=? y) && (y <=? 57)))) 0 256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lts_shl56 : forall b : byte,
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned b) 56)) (Z_to_bv 64 0) = (128 <=? bv_unsigned b).
Proof.
  intros b. apply Bool.eqb_prop. apply (codec_text.all_from_spec _ 256 0 lts_shl56_check).
  pose proof (byte_range b). lia.
Qed.

Lemma digit_ltu : forall b : byte,
  bv_ltu (Z_to_bv 64 8) (Z_to_bv 64 (Z.land ((bv_unsigned b + -49) mod 18446744073709551616) 255)) =
  negb ((49 <=? bv_unsigned b) && (bv_unsigned b <=? 57)).
Proof.
  intros b. apply Bool.eqb_prop. apply (codec_text.all_from_spec _ 256 0 digit_check).
  pose proof (byte_range b). lia.
Qed.

Lemma zb_cons : forall (x : byte) l, zb (x :: l) = bv_unsigned x :: zb l.
Proof. reflexivity. Qed.

Section Walk.
  Variables (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n : Z) (tb : list byte).
  Hypothesis HA0 : bv_unsigned a0 <> 0.
  Hypothesis HTZ : In (b8 0) tb.
  Hypothesis HA1 : bv_unsigned a1 <> 0.
  Hypothesis HA2 : bv_unsigned a2 = n.
  Hypothesis HDJ : disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) n.
  Hypothesis HSP0 : bv_unsigned sp <= bv_unsigned a0.
  Hypothesis HSP1 : bv_unsigned sp <= bv_unsigned a1.
  Hypothesis HLO : lo + 16 <= bv_unsigned sp.
  Hypothesis MEMS : memset_contract.

  Notation TX := (bv_unsigned a0).
  Notation OX := (bv_unsigned a1).
  Notation SP := (bv_unsigned sp).

  Definition INV (m1 : word -> option byte) (ob : list byte) : Prop :=
    bytes_at rsegs m1 TX tb /\ u8arr rsegs m1 OX ob /\ length ob = Z.to_nat n /\
    rw_cells rsegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk rsegs m1 lo (SP + -16) /\
    mem_inv rsegs m1 /\ munch [(SP + -16, SP); (OX, OX + n)] m m1 /\ wmono rsegs m m1.

  Definition POSTv (ov : list Z) (r : Z) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(SP - DIGINET_SCRIBBLE_TEXT_DEPTH, SP); (OX, OX + n)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
      a0' = Z_to_bv 64 r /\ rw_cells rsegs m' OX [CB (Z.to_nat n) (bz ov)].

  (** The epilogue at 0x15a3c: a0 := s0, restore ra and s0, pop the frame, return. *)
  Lemma epi : forall m1 ov r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 (bz ov) ->
    evt rsegs (POSTv ov r)
      (MS (mkR x1 (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 (Z_to_bv 64 r) s1 x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15a3c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros m1 ov r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           (TBi & OUTi & LEN & FR & ST & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply rw_cells_of_u8arr in OUTi. rewrite LEN in OUTi.
    finish.
    all: try (unfold DIGINET_SCRIBBLE_TEXT_DEPTH; replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU).
    all: reflexivity.
  Qed.

  (** The pad at 0x15a28: memset(out + o, ' ', n - o) when o < n. *)
  Lemma pad : forall m1 ob o pre ov r x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 ob -> 0 <= o <= n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
    x13 = Z_to_bv 64 o -> x8 = Z_to_bv 64 r -> ov = pre ++ repeat 0x20 (Z.to_nat (n - o)) ->
    evt rsegs (POSTv ov r)
      (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 x8 s1 x10 a1 a2 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15a28) fc None m1 (seg_rom rsegs)).
  Proof.
    intros m1 ob o pre ov r x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 I Ho Hl Hp -> -> ->.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & FR & ST & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    zstep. if_cases K; zify_cond K.
    - assert (o = n) by lia. subst o.
      replace (Z.to_nat (n - n)) with 0%nat by lia. cbn [repeat]. rewrite app_nil_r.
      rewrite firstn_all2 in Hp by lia. rewrite Hp in I0.
      apply epi. exact I0.
    - rewrite HA2 in K.
      pose proof (u8arr_split rsegs m1 _ ob (Z.to_nat o) ltac:(lia) OUTi) as [PRE1 SUF1]. clear OUTi.
      rewrite Z2Nat.id in SUF1 by lia.
      zstep. zstep. zstep. zstep.
      eapply evt_cut; [ eapply MEMS; [ | exact MI ] | ].
      { rewrite !unsigned_lit by lia. rewrite HA2.
        replace (Z.to_nat (n - o)) with (length (skipn (Z.to_nat o) ob)) by (rewrite length_skipn; lia).
        apply rw_cells_of_u8arr. exact SUF1. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  -> & MU2 & WM2 & MI2 & RW2).
      rewrite !unsigned_lit in MU2, RW2 by lia. rewrite HA2 in MU2, RW2.
      pose proof (bytes_at_transport _ _ _ _ _ _ TBi MU2 ltac:(cbn [disjoint_from]; unfold disj in HDJ; lia)) as TB2.
      pose proof (rw_cells_transport _ _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from]; cbn; lia)) as FR2.
      pose proof (stk_transport_disjoint _ _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST2.
      pose proof (u8arr_transport _ _ _ _ _ _ PRE1 MU2 WM2
                    ltac:(cbn [disjoint_from]; rewrite firstn_length_le by lia; lia)) as PRE2.
      assert (MU3 : munch [(SP + -16, SP); (OX, OX + n)] m m2).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
        unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      pose proof (wmono_trans _ _ _ _ WM WM2) as WM3.
      apply u8arr_of_rw_cells in RW2.
      replace (OX + o) with (OX + Z.of_nat (length (firstn (Z.to_nat o) ob))) in RW2
        by (rewrite firstn_length_le by lia; lia).
      pose proof (u8arr_join rsegs m2 _ _ _ PRE2 RW2) as J. rewrite Hp in J.
      lazymatch type of J with context [repeat ?b _] =>
        replace b with (b8 0x20) in J by (vm_compute; reflexivity) end.
      replace (bz pre ++ repeat (b8 32) (Z.to_nat (n - o))) with (bz (pre ++ repeat 0x20 (Z.to_nat (n - o)))) in J
        by (unfold bz; rewrite map_app, map_repeat; reflexivity).
      replace (ret_pc (Z_to_bv 64 88636)) with (Z_to_bv 64 88636) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      apply epi.
      split; [exact TB2|]. split; [exact J|]. split.
      { unfold bz. rewrite length_map, length_app, repeat_length. lia. }
      split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact MU3| exact WM3].
  Qed.

  Lemma inv_store : forall m1 ob o b, INV m1 ob -> 0 <= o < n ->
    INV (write_to_mem m1 (wa (OX + o)) [b]) (upd ob (Z.to_nat o) b).
  Proof.
    intros m1 ob o b (TBi & OUTi & LEN & FR & ST & MI & MU & WM) Ho.
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (u8arr_store_ok rsegs m1 _ ob o _ OUTi ltac:(rewrite LEN; lia) eq_refl) as HS.
    unfold disj in HDJ.
    split; [apply bytes_at_write_other; [exact TBi | lia | cbn; lia | cbn; lia]|].
    split; [apply u8arr_write; [exact OUTi | rewrite LEN; lia]|].
    split; [rewrite upd_length; exact LEN|].
    split; [apply rw_cells_frame; [exact FR | lia | cbn; lia | cbn; lia]|].
    split; [apply stk_write; [exact ST | lia | cbn; lia]|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    split; [apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia]|].
    apply wmono_write. exact WM.
  Qed.

  Lemma out_store_ok : forall m1 ob o, INV m1 ob -> 0 <= o < n -> store_ok rsegs m1 (wa (OX + o)) 1 = true.
  Proof.
    intros m1 ob o (TBi & OUTi & LEN & _) Ho.
    exact (u8arr_store_ok rsegs m1 _ ob o _ OUTi ltac:(rewrite LEN; lia) eq_refl).
  Qed.

  Lemma text_read : forall m1 ob j b, INV m1 ob -> nth_error tb j = Some b ->
    ov_read_bytes rsegs m1 (wa (TX + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros m1 ob j b (TBi & _) E.
    apply (u8ro_read rsegs m1 (bv_unsigned a0) tb (Z.of_nat j) b); [exact TBi | rewrite Nat2Z.id; exact E | lia | reflexivity].
  Qed.

  Definition HEADP (k : nat) : Prop :=
    forall i o pre ov r m1 ob b x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      (length tb - i = k)%nat ->
      INV m1 ob -> 0 <= o < n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
      nth_error tb i = Some b -> bv_unsigned b <> 0 -> In (b8 0) (skipn i tb) ->
      x8 = Z_to_bv 64 (Z.of_nat i) -> x13 = Z_to_bv 64 o -> x14 = zxb b -> x15 = Z_to_bv 64 (TX + 1) ->
      x16 = Z_to_bv 64 0x2e -> x17 = Z_to_bv 64 8 ->
      ov = pre ++ fst (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      r = Z.of_nat i + snd (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 x8 s1 a0 a1 a2 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x159bc) fc None m1 (seg_rom rsegs)).

  (** The common tail of an iteration at 0x159f4: store v at out[o], advance i by d, read the next byte. *)
  Lemma tail : forall k, (forall k', (k' < k)%nat -> HEADP k') ->
    forall i o pre ov r m1 ob v d x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      (length tb - i = k)%nat -> (1 <= d <= 2)%nat ->
      INV m1 ob -> 0 <= o < n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
      In (b8 0) (skipn (i + d) tb) ->
      scr_lib (zb (skipn i tb)) (Z.to_nat (n - o)) =
        (v :: fst (scr_lib (zb (skipn (i + d) tb)) (Z.to_nat (n - (o + 1)))),
         snd (scr_lib (zb (skipn (i + d) tb)) (Z.to_nat (n - (o + 1)))) + Z.of_nat d) ->
      le1 x14 = [b8 v] ->
      x5 = Z_to_bv 64 (Z.of_nat d) -> x8 = Z_to_bv 64 (Z.of_nat i) -> x13 = Z_to_bv 64 o ->
      x15 = Z_to_bv 64 (TX + 1) -> x16 = Z_to_bv 64 0x2e -> x17 = Z_to_bv 64 8 ->
      ov = pre ++ fst (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      r = Z.of_nat i + snd (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 x8 s1 a0 a1 a2 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x159f4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros k IH i o pre ov r m1 ob v d x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31
           Hk Hd I Ho Hl Hp HZ SPEC HV -> -> -> -> -> -> Hov Hr.
    rewrite SPEC in Hov, Hr. cbn [fst snd] in Hov, Hr. clear SPEC.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & FR & ST & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ TBi) as TBB.
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (out_store_ok m1 ob o I0 Ho) as HS.
    zstep. zstep. zstep. rewrite HV.
    pose proof (inv_store m1 ob o (b8 v) I0 Ho) as I2. unfold wa in I2.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (OX + o)) [b8 v]) in *. clearbody m2.
    clear TBi OUTi FR ST MI MU WM HS I0.
    assert (Hlt : (i + d < length tb)%nat) by (eapply In_skipn_lt; exact HZ).
    set (b' := nth (i + d) tb (b8 0)).
    pose proof (nth_error_nth' tb (i + d) (b8 0) Hlt) as E'. fold b' in E'.
    pose proof (text_read m2 _ (i + d) b' I2 E') as HR.
    pose proof (Hp_snoc ob o (b8 v) (bz pre) ltac:(lia) ltac:(lia) Hp) as Hp2.
    replace (bz pre ++ [b8 v]) with (bz (pre ++ [v])) in Hp2 by (unfold bz; rewrite map_app; reflexivity).
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb in K.
    - (* the next byte is the terminator: pad *)
      rewrite (skipn_nth_cons tb (i + d) (b8 0) Hlt) in Hov, Hr. fold b' in Hov, Hr.
      rewrite zb_cons, K, scr_zero in Hov, Hr. cbn [fst snd] in Hov, Hr.
      eapply (pad m2 _ (o + 1) (pre ++ [v]));
        [exact I2 | lia | rewrite length_app; cbn; lia | exact Hp2 | reflexivity | rewrite Hr; f_equal; lia | ].
      rewrite Hov, <- app_assoc. reflexivity.
    - zstep. if_cases K2; zify_cond K2.
      + (* o + 1 < n: next iteration *)
        rewrite HA2 in K2.
        pose proof (IH (length tb - (i + d))%nat ltac:(lia)) as IH'. unfold HEADP in IH'.
        eapply (IH' (i + d)%nat (o + 1) (pre ++ [v])); [reflexivity | exact I2 | lia | rewrite length_app; cbn; lia | exact Hp2 | exact E' | exact K
                    | exact HZ | f_equal; lia | reflexivity | reflexivity | reflexivity
                    | reflexivity | reflexivity | | ].
        * rewrite Hov, <- app_assoc. reflexivity.
        * rewrite Hr. lia.
      + (* o + 1 = n: pad nothing *)
        rewrite HA2 in K2.
        zstep.
        replace (Z.to_nat (n - (o + 1))) with 0%nat in Hov, Hr by lia. rewrite scr_lib_0 in Hov, Hr.
        cbn [fst snd] in Hov, Hr.
        eapply (pad m2 _ (o + 1) (pre ++ [v]));
          [exact I2 | lia | rewrite length_app; cbn; lia | exact Hp2 | reflexivity | rewrite Hr; f_equal; lia | ].
        rewrite Hov. replace (Z.to_nat (n - (o + 1))) with 0%nat by lia. cbn [repeat].
        rewrite app_nil_r. reflexivity.
  Qed.

  (** The non-'.'+digit path at 0x159e4: the byte as is below 0x80, else '?'; then the tail with d = 1. *)
  Lemma other : forall k, (forall k', (k' < k)%nat -> HEADP k') ->
    forall i o pre ov r m1 ob b x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      (length tb - i = k)%nat ->
      INV m1 ob -> 0 <= o < n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
      In (b8 0) (skipn (i + 1) tb) ->
      scr_lib (zb (skipn i tb)) (Z.to_nat (n - o)) =
        ((if bv_unsigned b <? 0x80 then bv_unsigned b else 0x3f)
           :: fst (scr_lib (zb (skipn (i + 1) tb)) (Z.to_nat (n - (o + 1)))),
         snd (scr_lib (zb (skipn (i + 1) tb)) (Z.to_nat (n - (o + 1)))) + Z.of_nat 1) ->
      x8 = Z_to_bv 64 (Z.of_nat i) -> x13 = Z_to_bv 64 o -> x14 = zxb b ->
      x15 = Z_to_bv 64 (TX + 1) -> x16 = Z_to_bv 64 0x2e -> x17 = Z_to_bv 64 8 ->
      ov = pre ++ fst (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      r = Z.of_nat i + snd (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 x8 s1 a0 a1 a2 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x159e4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros k IH i o pre ov r m1 ob b x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31
           Hk I Ho Hl Hp HZ SPEC -> -> -> -> -> -> Hov Hr.
    pose proof (byte_range b) as Rb.
    zstep. zstep. rewrite lts_shl56.
    destruct (Z.leb_spec 128 (bv_unsigned b)) as [Hhi|Hlo]; cbn [negb].
    - rewrite (proj2 (Z.ltb_ge _ _) Hhi) in SPEC.
      zstep. zstep.
      eapply (tail k IH i o pre ov r m1 ob 63 1%nat); try reflexivity; try eassumption; try lia.
    - rewrite (proj2 (Z.ltb_lt _ _) Hlo) in SPEC.
      zstep.
      eapply (tail k IH i o pre ov r m1 ob (bv_unsigned b) 1%nat); try reflexivity; try eassumption; try lia.
      all: exact (le1_lit _).
  Qed.

  Lemma head : forall k, HEADP k.
  Proof.
    intros k. induction k as [k IH] using lt_wf_ind. unfold HEADP.
    intros i o pre ov r m1 ob b x5 x6 x7 x8 x13 x14 x15 x16 x17 x28 x29 x30 x31
           Hk I Ho Hl Hp Eb Hb HZ -> -> -> -> -> -> Hov Hr.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & FR & ST & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ TBi) as TBB.
    pose proof (byte_range b) as Rb.
    assert (Hi : (i < length tb)%nat) by (eapply In_skipn_lt; exact HZ).
    assert (Eb' : nth i tb (b8 0) = b).
    { rewrite (nth_error_nth' tb i (b8 0) Hi) in Eb. inversion Eb. reflexivity. }
    assert (HZ1 : In (b8 0) (skipn (S i) tb)).
    { rewrite (skipn_nth_cons tb i (b8 0) Hi), Eb' in HZ. destruct HZ as [H0|H0]; [|exact H0].
      exfalso. apply Hb. rewrite H0. reflexivity. }
    assert (Hi1 : (S i < length tb)%nat) by (eapply In_skipn_lt; exact HZ1).
    set (b2 := nth (S i) tb (b8 0)).
    pose proof (nth_error_nth' tb (S i) (b8 0) Hi1) as E2. fold b2 in E2.
    pose proof (byte_range b2) as Rb2.
    assert (SK1 : zb (skipn (i + 1) tb) = bv_unsigned b2 :: zb (skipn (i + 2) tb)).
    { replace (i + 1)%nat with (S i) by lia. rewrite (skipn_nth_cons tb (S i) (b8 0) Hi1). fold b2.
      replace (i + 2)%nat with (S (S i)) by lia. reflexivity. }
    assert (SK : zb (skipn i tb) = bv_unsigned b :: bv_unsigned b2 :: zb (skipn (i + 2) tb)).
    { rewrite (skipn_nth_cons tb i (b8 0) Hi), Eb', zb_cons. f_equal. rewrite <- SK1. f_equal. f_equal. lia. }
    assert (KN : Z.to_nat (n - o) = S (Z.to_nat (n - (o + 1)))) by lia.
    pose proof (scr_step (bv_unsigned b) (bv_unsigned b2) (zb (skipn (i + 2) tb)) (Z.to_nat (n - (o + 1))) Hb) as STEP.
    rewrite <- SK, <- KN, <- SK1 in STEP.
    zstep. zstep. rewrite (land255 (bv_unsigned b) Rb).
    if_cases K; zify_cond K.
    - (* the byte is not '.' *)
      rewrite (proj2 (Z.eqb_neq _ _) K) in STEP. cbn [andb] in STEP.
      eapply (other k IH i o pre ov r m1 ob b); try reflexivity; try eassumption; try lia.
      replace (i + 1)%nat with (S i) by lia. exact HZ1.
    - (* '.': look at the next byte *)
      pose proof (text_read m1 ob (S i) b2 I0 E2) as HR.
      zstep. zstep. zstep. zstep. zstep. rewrite digit_ltu.
      rewrite (proj2 (Z.eqb_eq _ _) K) in STEP. cbn [andb] in STEP.
      destruct ((49 <=? bv_unsigned b2) && (bv_unsigned b2 <=? 57)) eqn:D; cbn [negb].
      + (* '.' and a digit 1..9: one output byte, two text bytes *)
        assert (HZ2 : In (b8 0) (skipn (i + 2) tb)).
        { rewrite (skipn_nth_cons tb (S i) (b8 0) Hi1) in HZ1. fold b2 in HZ1.
          destruct HZ1 as [H0|H0].
          - exfalso. apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1.
            rewrite H0 in D1. change (bv_unsigned (b8 0)) with 0 in D1. lia.
          - replace (i + 2)%nat with (S (S i)) by lia. exact H0. }
        zstep. zstep. zstep.
        eapply (tail k IH i o pre ov r m1 ob (bv_unsigned b2 - 26) 2%nat); try reflexivity; try eassumption; try lia.
        exact (le1_lit _).
      + eapply (other k IH i o pre ov r m1 ob b); try reflexivity; try eassumption; try lia.
        all: try (replace (i + 1)%nat with (S i) by lia; exact HZ1).
        all: rewrite STEP, (proj2 (Z.eqb_eq _ _) K); reflexivity.
  Qed.

  (** The entry at 0x15980: the frame, the NULL tests, the first byte and n == 0, then the loop. *)
  Lemma entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (oj : list byte),
    bytes_at rsegs m TX tb -> rw_cells rsegs m OX [CB (Z.to_nat n) oj] -> mem_inv rsegs m -> stk rsegs m lo SP ->
    evt rsegs (POSTv (fst (scribble_text_spec (zb tb) n)) (snd (scribble_text_spec (zb tb) n)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15980) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 oj TB OUT MI ST.
    unfold scribble_text_spec.
    pose proof (munch_refl [(SP + -16, SP); (OX, OX + n)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2.
    pose proof (rw_cells_bound _ _ _ _ OUT) as OB. cbn [cells_size csize] in OB.
    carve_frame 16%nat ST.
    zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    assert (LEN : length oj = Z.to_nat n) by (destruct OUT as [[[Hw _] _] _]; exact Hw).
    apply u8arr_of_rw_cells in OUT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (I : INV mm oj) by (unfold INV; split; [exact TB|]; split; [exact OUT|]; split; [exact LEN|];
        split; [exact FR|]; split; [exact ST|]; split; [exact MI|]; split; [exact MU|exact WM]) end.
    assert (Hl0 : (0 < length tb)%nat) by (destruct tb; [destruct HTZ | cbn; lia]).
    set (b0 := nth 0 tb (b8 0)).
    pose proof (nth_error_nth' tb 0 (b8 0) Hl0) as E0. fold b0 in E0.
    pose proof (text_read _ _ 0 b0 I E0) as HR.
    replace (wa (TX + Z.of_nat 0)) with a0 in HR by (unfold wa; cbn [Z.of_nat]; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self).
    pose proof (byte_range b0) as Rb0.
    assert (ZB : zb tb = bv_unsigned b0 :: zb (skipn 1 tb)).
    { rewrite <- zb_cons. f_equal. exact (skipn_nth_cons tb 0 (b8 0) Hl0). }
    zstep. zstep. zstep.
    zstep. if_cases K1; zify_cond K1; rewrite ?u_zxb in K1.
    - (* the text is empty: pad all n *)
      eapply (pad _ oj 0 []); try exact I; try lia; try reflexivity.
      + rewrite ZB, K1, scr_zero. reflexivity.
      + rewrite ZB, K1, scr_zero. cbn [fst app]. replace (n - 0) with n by lia. reflexivity.
    - zstep. if_cases K2; zify_cond K2.
      + (* n = 0 *)
        rewrite HA2 in K2. replace (Z.to_nat n) with 0%nat by lia. rewrite scr_lib_0.
        eapply (pad _ oj 0 []); try exact I; try lia; try reflexivity.
        cbn [fst]. replace (Z.to_nat (n - 0)) with 0%nat by lia. reflexivity.
      + rewrite HA2 in K2.
        zstep. zstep. zstep. zstep. zstep.
        eapply (head (length tb - 0) 0%nat 0 []); try exact I; try exact E0; try reflexivity; try lia.
        * cbn [skipn]. exact HTZ.
        * cbn [skipn app]. replace (n - 0) with n by lia. reflexivity.
        * cbn [skipn]. replace (n - 0) with n by lia. reflexivity.
  Qed.

End Walk.

Theorem diginet_scribble_text_holds : memset_contract -> diginet_scribble_text_contract.
Proof.
  intros MEMS. unfold diginet_scribble_text_contract, DIGINET_SCRIBBLE_TEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo n tb oj PRE.
  unfold diginet_scribble_text_pre, DIGINET_SCRIBBLE_TEXT_DEPTH in PRE.
  destruct PRE as (A0 & [TB TZ] & A1 & A2 & OUT & DJ & SP0 & SP1 & MI & ST & LO).
  eapply entry; eassumption.
Qed.
