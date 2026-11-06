From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_main_inv
  diginet_fader_encode_c diginet_button_encode_c diginet_touch_encode_c
  diginet_vpot_encode_c diginet_jog_encode_c diginet_ring_encode_c diginet_meter_encode_c
  diginet_strip_leds_encode_c diginet_counter_leds_encode_c diginet_scribble_encode_c
  diginet_counter_encode_c diginet_sysex_encode_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the record around an encoder call: the 108 bytes before k.out, k.out, the 44 after ---- *)

Definition kpre (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)].

Definition kpost (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

Lemma fr_split : forall E m1 k cur nl u0 pj tj plj,
  fr E m1 (kcall_cells k) cur nl u0 pj tj plj ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kpre k) /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -276) [CB 32 (k_out k)] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -244) (kpost k) /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 cur; C8 nl] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E).
Proof.
  intros E m1 k cur nl u0 pj tj plj (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite kcall_cells_split_out in FK.
  apply rw_cells_app_split in FK. destruct FK as [FPRE FK]. rewrite kcall_pre_size in FK.
  apply rw_cells_app_split in FK. destruct FK as [FOUT FPOST]. cbn [cells_size csize Nat.add] in FPOST.
  replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 108) with (bv_unsigned (c_sp E) + -276) in FOUT, FPOST by lia.
  replace (bv_unsigned (c_sp E) + -276 + Z.of_nat 32) with (bv_unsigned (c_sp E) + -244) in FPOST by lia.
  exact (conj F0 (conj F8 (conj FPRE (conj FOUT (conj FPOST (conj FIN (conj FPD (conj FTX (conj FPL FSV))))))))).
Qed.

Lemma fr_join : forall E m1 k o cur nl u0 pj tj plj,
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kpre k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -276) [CB 32 (cmd_out (k_before k) o)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -244) (kpost k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 cur; C8 nl] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  fr E m1 (kcall_cells (with_out k o)) cur nl u0 pj tj plj.
Proof.
  intros E m1 k o cur nl u0 pj tj plj F0 F8 FPRE FOUT FPOST FIN FPD FTX FPL FSV.
  refine (conj (kcall_cells_size _) (conj F0 (conj F8 (conj _ (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))).
  rewrite kcall_cells_split_out. unfold with_out.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
       k_want_rc k_want k_want_len k_want_key k_want_display].
  apply rw_cells_app_join; [exact FPRE|]. rewrite kcall_pre_size.
  apply rw_cells_app_join.
  - replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 108) with (bv_unsigned (c_sp E) + -276) by lia. exact FOUT.
  - cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 108 + Z.of_nat 32) with (bv_unsigned (c_sp E) + -244) by lia.
    exact FPOST.
Qed.

(** ---- loads of part of a 4-byte cell (lbu / lhu of k.a, k.b) ---- *)

Lemma rw_cells_cell_bytes : forall m A cs k c,
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[Hwf Hb] _] Hc.
  destruct (cell_at_split cs k c c Hc) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [W1 _].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (cells_bytes_length pre W1), Hsz in Hb.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma c4_byte0 : forall m A cs k v,
  rw_cells rsegs m A cs -> cell_at cs k = Some (C4 v) ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A cs k v H Hc. pose proof (rw_cells_cell_bytes m A cs k (C4 v) H Hc) as B.
  cbn [cbytes] in B.
  replace (A + Z.of_nat k) with (A + Z.of_nat k + 0) by lia.
  rewrite (bytes_at_read rsegs m _ (le4 v) 0 1 B) by (rewrite ?length_le4; cbn; lia).
  reflexivity.
Qed.

Lemma c4_half0 : forall m A cs k v,
  rw_cells rsegs m A cs -> cell_at cs k = Some (C4 v) ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 2 = Some (le2 v).
Proof.
  intros m A cs k v H Hc. pose proof (rw_cells_cell_bytes m A cs k (C4 v) H Hc) as B.
  cbn [cbytes] in B.
  replace (A + Z.of_nat k) with (A + Z.of_nat k + 0) by lia.
  rewrite (bytes_at_read rsegs m _ (le4 v) 0 2 B) by (rewrite ?length_le4; cbn; lia).
  reflexivity.
Qed.

Lemma bytes_at_firstn : forall m a bs j, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn j bs).
Proof.
  intros m a bs j H. rewrite <- (firstn_skipn j bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(** ---- register values ---- *)

Lemma sx32_u32 : forall v, 0 <= v < 2 ^ 32 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (s32 v).
Proof.
  intros v Hv. unfold sx32, s32. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Lemma lbu_val : forall v, 0 <= v < 2 ^ 64 ->
  zxb (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))) = Z_to_bv 64 (v mod 256).
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite (unsigned_lit v Hv). rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma lhu_val : forall v, 0 <= v < 2 ^ 64 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 (v mod 2 ^ 16).
Proof. intros v Hv. unfold zx16. rewrite (unsigned_lit v Hv). reflexivity. Qed.

Lemma s32_range : forall c, 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= s32 c < 2 ^ 31.
Proof. intros c Hc. unfold s32. destruct (Z.ltb_spec c (2 ^ 31)); lia. Qed.

Lemma mod16_4 : forall x c, x mod 16 = 0 -> c mod 4 = 0 -> (x + c) mod 4 = 0.
Proof.
  intros x c Hx Hc. rewrite Z.add_mod by lia. rewrite Hc.
  assert (x mod 4 = 0).
  { pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D. rewrite D.
    replace (16 * (x / 16)) with ((4 * (x / 16)) * 4) by lia. apply Z.mod_mul. lia. }
  rewrite H. reflexivity.
Qed.

(** ---- the personality argument and its disjointness from the callee's frame and out ---- *)

Lemma od_some : forall k d, od_of k = Some d -> d = c24 \/ d = pc.
Proof.
  intros k d H. unfold od_of in H.
  destruct (k_desk k =? SDESK_C24); [left; congruence|].
  destruct (k_desk k =? SDESK_PC); [right; congruence | discriminate].
Qed.

Lemma desk_some : forall k d, desk_at k -> od_of k = Some d -> k_p k = PERS \/ k_p k = PERS + 24.
Proof.
  intros k d [(Hp & Hd) | [(Hp & Hd) | (Hp & Hd)]] Ho; [| left; exact Hp | right; exact Hp].
  unfold od_of in Ho. rewrite Hd in Ho. discriminate Ho.
Qed.

Lemma pers_arg_k : forall m k, relro_img m -> desk_at k -> pers_arg m (Z_to_bv 64 (k_p k)) (od_of k).
Proof.
  intros m k HR [(Hp & Hd) | [(Hp & Hd) | (Hp & Hd)]].
  - replace (od_of k) with (@None desk) by (unfold od_of; rewrite Hd; reflexivity).
    cbn [pers_arg]. rewrite Hp. reflexivity.
  - replace (od_of k) with (Some c24) by (unfold od_of; rewrite Hd; reflexivity).
    cbn [pers_arg]. rewrite Hp, unsigned_lit by (unfold PERS; lia).
    split; [unfold PERS; lia|]. split; [reflexivity|].
    split; [unfold desk_ok; cbn; lia|].
    apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HR | cbn; unfold PERS, codec_relro_base; lia .. |].
    vm_compute. reflexivity.
  - replace (od_of k) with (Some pc) by (unfold od_of; rewrite Hd; reflexivity).
    cbn [pers_arg]. rewrite Hp, unsigned_lit by (unfold PERS; lia).
    split; [unfold PERS; lia|]. split; [reflexivity|].
    split; [unfold desk_ok; cbn; lia|].
    apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HR | cbn; unfold PERS, codec_relro_base; lia .. |].
    vm_compute. reflexivity.
Qed.

(** The personality fields p + 16 .. p + 19 lie in the RELRO block, which the contract keeps off the
    stack window [lo, sp): so they are off any area of the window. *)
Lemma pers_disj : forall k d lo s a b,
  desk_at k -> od_of k = Some d ->
  disj lo (s - lo) RELRO_BASE RELRO_LEN -> lo <= a -> a + b <= s ->
  disj (bv_unsigned (Z_to_bv 64 (k_p k)) + 16) 4 a b.
Proof.
  intros k d lo s a b HD Ho DJ H1 H2.
  destruct (desk_some k d HD Ho) as [Hp | Hp]; rewrite Hp, unsigned_lit by (unfold PERS; lia);
    unfold disj, RELRO_BASE, RELRO_LEN, PERS in *; lia.
Qed.

(** ---- the per-kind preamble ---- *)

Ltac run_pre :=
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CT JOIN k RW HK;
  unfold rec_ok;
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         RW' HN HOPS HCUR HC0 HCN FR ST MU WM HMI;
  clear RW';
  pose proof (relro_at _ m1 ENV MU) as RI1;
  pose proof (JOIN k RW) as J; clear JOIN;
  unfold join_ok in J;
  apply fr_split in FR;
  unfold env_ok in ENV;
  cenv_cbn;
  destruct FR as (F0 & F8 & FPRE & FOUT & FPOST & FIN & FPD & FTX & FPL & FSV);
  destruct ENV as (_ & _ & _ & LO & SPA & _ & _ & _ & _ & DJR);
  pose proof ST as (Hlo & Hhi & _);
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
  pose proof RW as (Hk & HDESK & HBEF & HOUT & _ & _ & _ & _ & _ & RD);
  destruct RD as (Ra & Rb & Rc & Rd & Rlen & _ & Rn & _ & _ & _);
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -416)) = bv_unsigned sp + -416)
    by (apply unsigned_lit; lia);
  assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -276)) = bv_unsigned sp + -276)
    by (apply unsigned_lit; lia);
  assert (A4 : (bv_unsigned sp + -276) mod 4 = 0) by (apply mod16_4; [exact SPA | reflexivity]);
  clear SPA;
  pose proof (pers_arg_k m1 k RI1 HDESK) as PA;
  unfold kpre in FPRE.

(** The pre of an encoder: every conjunct is a hypothesis, a disjointness of the personality, an
    equation of the register, or arithmetic. *)
Ltac rw_units := repeat match goal with H : bv_unsigned (Z_to_bv 64 (_ + _)) = _ |- _ => progress rewrite H end.

Ltac pre_tac :=
  rw_units;
  unfold arg_u32, arg_s32, arg_zx;
  repeat (lazymatch goal with |- _ /\ _ => split end);
  first [ eassumption
        | reflexivity
        | (let d := fresh "d" in let Hd := fresh "Hd" in intros d Hd;
           first [ eapply pers_disj; [eassumption | exact Hd | eassumption | lia | lia]
                 | destruct (od_some _ _ Hd) as [-> | ->]; cbn; lia ])
        | (unfold disj; lia) ].

(** After the call: the code in a0, out rewritten, the stack register as the frame base. *)
Ltac post_tac SPEC POST U276 U416 :=
  let rc := fresh "rc" in let o := fresh "o" in let ES := fresh "ES" in
  let HA0 := fresh "HA0" in let HO := fresh "HO" in
  destruct SPEC as [rc o] eqn:ES;
  destruct POST as [HA0 HO];
  match type of HA0 with ?x = _ => subst x end;
  rewrite ?U276 in HO;
  rewrite ?U416 in *.

(** The join at 0x144cc. *)
Ltac join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT :=
  rewrite EK in J; cbn [fst snd] in J;
  eapply J; [ exact RW | exact HN | exact HOPS | exact HCUR | exact HC0 | exact HCN | | eassumption .. ];
  apply fr_join; try eassumption;
  match goal with |- rw_cells _ _ _ [CB 32 (cmd_out (k_before ?k) ?o)] =>
    replace (cmd_out (k_before k) o) with (cmd_out (k_out k) o) by (rewrite HBEF, HOUT; reflexivity) end;
  eassumption.

(** ---- the arms of run() (fuzz_codec.c:533-547) ---- *)

(** The encoder call: [eapply] its contract with the given parameters, prove the pre, take the post. *)
Ltac call_enc CT ARGS :=
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ ARGS CT | post_call rsegs mm ] end.

(** 0x143b4: diginet_fader_encode(k.p, k.a, k.b, &k.out). *)
Lemma run_k0 : forall E n, env_ok E -> diginet_fader_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 0 -> rec_ok E n k 0x143b4.
Proof.
  run_pre.
  unfold diginet_fader_encode_contract, diginet_fader_encode_pre, DIGINET_FADER_ENCODE in CT.
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_u32 (k_b k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (pd := od_of k) (strip := k_a k) (value := k_b k) (before := k_out k)).
  { pre_tac. }
  post_tac (fader_spec (od_of k) (k_a k) (k_b k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x14454: diginet_button_encode(k.a, k.b, k.c, &k.out). *)
Lemma run_k1 : forall E n, env_ok E -> diginet_button_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 1 -> rec_ok E n k 0x14454.
Proof.
  run_pre.
  unfold diginet_button_encode_contract, diginet_button_encode_pre, DIGINET_BUTTON_ENCODE in CT.
  pose proof (s32_range (k_c k) Rc) as Sc.
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_u32 (k_b k)), (sx32_u32 (k_c k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (button := k_a k) (id := k_b k) (on := s32 (k_c k)) (before := k_out k)).
  { pre_tac. }
  post_tac (button_spec (k_a k) (k_b k) (s32 (k_c k))) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x1440c: diginet_touch_encode(k.p, k.a, k.c, &k.out). *)
Lemma run_k2 : forall E n, env_ok E -> diginet_touch_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 2 -> rec_ok E n k 0x1440c.
Proof.
  run_pre.
  unfold diginet_touch_encode_contract, diginet_touch_encode_pre, DIGINET_TOUCH_ENCODE in CT.
  pose proof (s32_range (k_c k) Rc) as Sc.
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_u32 (k_c k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (pd := od_of k) (strip := k_a k) (on := s32 (k_c k)) (before := k_out k)).
  { pre_tac. }
  post_tac (touch_spec (od_of k) (k_a k) (s32 (k_c k))) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x14424: diginet_vpot_encode(k.p, k.a, k.delta, &k.out). *)
Lemma run_k3 : forall E n, env_ok E -> diginet_vpot_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 3 -> rec_ok E n k 0x14424.
Proof.
  run_pre.
  unfold diginet_vpot_encode_contract, diginet_vpot_encode_pre, DIGINET_VPOT_ENCODE in CT.
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_small (k_delta k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (pd := od_of k) (strip := k_a k) (delta := k_delta k) (before := k_out k)).
  { pre_tac. }
  post_tac (vpot_spec (od_of k) (k_a k) (k_delta k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x143fc: diginet_jog_encode(k.delta, &k.out). *)
Lemma run_k4 : forall E n, env_ok E -> diginet_jog_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 4 -> rec_ok E n k 0x143fc.
Proof.
  run_pre.
  unfold diginet_jog_encode_contract, diginet_jog_encode_pre, DIGINET_JOG_ENCODE in CT.
  step. step.
  rewrite (sx32_small (k_delta k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (delta := k_delta k) (before := k_out k)).
  { pre_tac. }
  post_tac (jog_spec (k_delta k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x1446c: diginet_ring_encode(k.p, k.a, (uint16_t) k.b, &k.out). *)
Lemma run_k5 : forall E n, env_ok E -> diginet_ring_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 5 -> rec_ok E n k 0x1446c.
Proof.
  run_pre.
  unfold diginet_ring_encode_contract, diginet_ring_encode_pre, DIGINET_RING_ENCODE,
    DIGINET_RING_ENCODE_DEPTH in CT.
  pose proof (c4_half0 _ _ _ 28 _ FPRE eq_refl) as HRH.
  replace (bv_unsigned sp + -384 + Z.of_nat 28) with (bv_unsigned sp + -356) in HRH by lia.
  step. step. step.
  rewrite (sx32_u32 (k_a k)) by lia.
  rewrite (lhu_val (k_b k)) by lia.
  clear HRH.
  step. step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (strip := k_a k) (mask := k_b k mod 2 ^ 16)
                                         (before := k_out k)).
  { pre_tac. }
  post_tac (ring_spec (od_of k) (k_a k) (k_b k mod 2 ^ 16)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x14484: diginet_meter_encode(k.p, k.a, k.c, k.b, &k.out). *)
Lemma run_k6 : forall E n, env_ok E -> diginet_meter_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 6 -> rec_ok E n k 0x14484.
Proof.
  run_pre.
  unfold diginet_meter_encode_contract, diginet_meter_encode_pre, DIGINET_METER_ENCODE,
    DIGINET_METER_ENCODE_DEPTH in CT.
  pose proof (s32_range (k_c k) Rc) as Sc.
  step. step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_u32 (k_b k)), (sx32_u32 (k_c k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (channel := k_a k) (right := s32 (k_c k))
                                         (segments := k_b k) (before := k_out k)).
  { pre_tac. }
  post_tac (meter_spec (od_of k) (k_a k) (s32 (k_c k)) (k_b k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x1443c: diginet_strip_leds_encode(k.p, k.a, k.b, &k.out). *)
Lemma run_k7 : forall E n, env_ok E -> diginet_strip_leds_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 7 -> rec_ok E n k 0x1443c.
Proof.
  run_pre.
  unfold diginet_strip_leds_encode_contract, diginet_strip_leds_encode_pre, DIGINET_STRIP_LEDS_ENCODE,
    DIGINET_STRIP_LEDS_ENCODE_DEPTH in CT.
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)), (sx32_u32 (k_b k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (strip := k_a k) (bits := k_b k)
                                         (before := k_out k)).
  { pre_tac. }
  post_tac (strip_leds_spec (od_of k) (k_a k) (k_b k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x144a0: diginet_counter_leds_encode(k.p, k.b, &k.out). *)
Lemma run_k8 : forall E n, env_ok E -> diginet_counter_leds_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 8 -> rec_ok E n k 0x144a0.
Proof.
  run_pre.
  unfold diginet_counter_leds_encode_contract, diginet_counter_leds_encode_pre, DIGINET_COUNTER_LEDS_ENCODE,
    DIGINET_COUNTER_LEDS_ENCODE_DEPTH in CT.
  step. step. step.
  rewrite (sx32_u32 (k_b k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (bits := k_b k) (before := k_out k)).
  { pre_tac. }
  post_tac (counter_leds_spec (od_of k) (k_b k)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x143cc: diginet_scribble_encode(k.p, k.a, k.bytes, &k.out); SCRIBBLE_TEXT enters here. *)
Lemma run_k9 : forall E n, env_ok E -> diginet_scribble_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 9 -> rec_ok E n k 0x143cc.
Proof.
  run_pre.
  unfold diginet_scribble_encode_contract, diginet_scribble_encode_pre, DIGINET_SCRIBBLE_ENCODE,
    DIGINET_SCRIBBLE_ENCODE_DEPTH in CT.
  pose proof (rw_cells_cell_bytes _ _ _ 40 _ FPRE eq_refl) as HBY. cbn [cbytes] in HBY.
  replace (bv_unsigned sp + -384 + Z.of_nat 40) with (bv_unsigned sp + -344) in HBY by lia.
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -344)) = bv_unsigned sp + -344)
    by (apply unsigned_lit; lia).
  step. step. step. step.
  rewrite (sx32_u32 (k_a k)) by lia.
  step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (addr := k_a k) (cs := k_bytes k)
                                         (before := k_out k)).
  { pre_tac. }
  post_tac (scribble_spec (od_of k) (k_a k) (zb (k_bytes k))) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x143e4: diginet_counter_encode(k.p, k.bytes, (uint8_t) k.b, &k.out); COUNTER_TEXT enters here. *)
Lemma run_k10 : forall E n, env_ok E -> diginet_counter_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 10 -> rec_ok E n k 0x143e4.
Proof.
  run_pre.
  unfold diginet_counter_encode_contract, diginet_counter_encode_pre, DIGINET_COUNTER_ENCODE,
    DIGINET_COUNTER_ENCODE_DEPTH in CT.
  pose proof (c4_byte0 _ _ _ 28 _ FPRE eq_refl) as HRB.
  replace (bv_unsigned sp + -384 + Z.of_nat 28) with (bv_unsigned sp + -356) in HRB by lia.
  pose proof (rw_cells_cell_bytes _ _ _ 40 _ FPRE eq_refl) as HBY. cbn [cbytes] in HBY.
  replace (bv_unsigned sp + -384 + Z.of_nat 40) with (bv_unsigned sp + -344) in HBY by lia.
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -344)) = bv_unsigned sp + -344)
    by (apply unsigned_lit; lia).
  step. step.
  rewrite (lbu_val (k_b k)) by lia.
  clear HRB.
  step. step. step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (pd := od_of k) (dots := k_b k mod 256) (sg := k_bytes k)
                                         (before := k_out k)).
  { pre_tac. }
  post_tac (counter_spec (od_of k) (zb (k_bytes k)) (k_b k mod 256)) POST U276 U416.
  assert (EK : enc_k k = (rc, o)) by (unfold enc_k, enc_of_call; rewrite HK; exact ES).
  step.
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** 0x144b4: diginet_sysex_encode((uint8_t) k.a, (uint8_t) k.b, k.bytes, k.n, &k.out); it returns
    straight to 0x144cc. *)
Lemma run_k11 : forall E n, env_ok E -> diginet_sysex_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  forall k, rec_wf k -> k_kind k = 11 -> rec_ok E n k 0x144b4.
Proof.
  run_pre.
  unfold diginet_sysex_encode_contract, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE,
    DIGINET_SYSEX_ENCODE_DEPTH in CT.
  pose proof (c4_byte0 _ _ _ 24 _ FPRE eq_refl) as HRA.
  replace (bv_unsigned sp + -384 + Z.of_nat 24) with (bv_unsigned sp + -360) in HRA by lia.
  pose proof (c4_byte0 _ _ _ 28 _ FPRE eq_refl) as HRB.
  replace (bv_unsigned sp + -384 + Z.of_nat 28) with (bv_unsigned sp + -356) in HRB by lia.
  pose proof (rw_cells_cell_bytes _ _ _ 40 _ FPRE eq_refl) as HBY. cbn [cbytes] in HBY.
  replace (bv_unsigned sp + -384 + Z.of_nat 40) with (bv_unsigned sp + -344) in HBY by lia.
  apply (bytes_at_firstn _ _ _ (Z.to_nat (k_n k))) in HBY.
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -344)) = bv_unsigned sp + -344)
    by (apply unsigned_lit; lia).
  step. step.
  rewrite (lbu_val (k_a k)), (lbu_val (k_b k)) by lia.
  clear HRA HRB.
  step. step. step. step.
  call_enc CT ltac:(fun C => eapply C with (lo := lo) (dev := k_a k mod 256) (fn := k_b k mod 256)
                                         (pl := firstn (Z.to_nat (k_n k)) (k_bytes k)) (before := k_out k)).
  { rewrite U344, (unsigned_lit (k_n k)) by lia. rewrite length_firstn, LB.
    pre_tac. }
  post_tac (sysex_spec (k_a k mod 256) (k_b k mod 256) (zb (firstn (Z.to_nat (k_n k)) (k_bytes k)))) POST U276 U416.
  assert (EK : enc_k k = (rc, o))
    by (unfold enc_k, enc_of_call; rewrite HK; unfold zb in *; rewrite firstn_map; exact ES).
  join_tac J EK RW HN HOPS HCUR HC0 HCN HBEF HOUT.
Qed.

(** Every kind enters its arm. *)
Lemma run_arm : forall E n, env_ok E ->
  diginet_fader_encode_contract -> diginet_button_encode_contract -> diginet_touch_encode_contract ->
  diginet_vpot_encode_contract -> diginet_jog_encode_contract -> diginet_ring_encode_contract ->
  diginet_meter_encode_contract -> diginet_strip_leds_encode_contract ->
  diginet_counter_leds_encode_contract -> diginet_scribble_encode_contract ->
  diginet_counter_encode_contract -> diginet_sysex_encode_contract ->
  (forall k, rec_wf k -> join_ok E n k) ->
  rd_run_arm E n.
Proof.
  intros E n ENV C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 JOIN k RW.
  pose proof RW as (Hk & _).
  assert (Hc : k_kind k = 0 \/ k_kind k = 1 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 4 \/
               k_kind k = 5 \/ k_kind k = 6 \/ k_kind k = 7 \/ k_kind k = 8 \/ k_kind k = 9 \/
               k_kind k = 10 \/ k_kind k = 11) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]; rewrite H.
  - exact (run_k0 E n ENV C0 JOIN k RW H).
  - exact (run_k1 E n ENV C1 JOIN k RW H).
  - exact (run_k2 E n ENV C2 JOIN k RW H).
  - exact (run_k3 E n ENV C3 JOIN k RW H).
  - exact (run_k4 E n ENV C4 JOIN k RW H).
  - exact (run_k5 E n ENV C5 JOIN k RW H).
  - exact (run_k6 E n ENV C6 JOIN k RW H).
  - exact (run_k7 E n ENV C7 JOIN k RW H).
  - exact (run_k8 E n ENV C8 JOIN k RW H).
  - exact (run_k9 E n ENV C9 JOIN k RW H).
  - exact (run_k10 E n ENV C10 JOIN k RW H).
  - exact (run_k11 E n ENV C11 JOIN k RW H).
Qed.

(** 0x14390: lw a0, k.kind; bltu s11 (= 10), a0 to the SYSEX arm; else T2[kind] at 0x1047c. *)
Lemma run_switch : forall E n, env_ok E -> rd_run_arm E n -> rd_run E n.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV ARM k RW.
  unfold rec_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         RW' HN HOPS HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (ARM k RW) as A. clear ARM. unfold rec_ok in A.
  pose proof FR as FR0. apply fr_split in FR0.
  unfold env_ok in ENV.
  cenv_cbn.
  destruct FR0 as (_ & _ & FPRE & _). unfold kpre in FPRE.
  pose proof RW as (Hk & _).
  step.
  rewrite (sx32_small (k_kind k)) by lia.
  step.
  if_cases G.
  - zify_cond G.
    assert (H : k_kind k = 11) by lia.
    rewrite H in A. change (pc_run 11) with 0x144b4 in A.
    eapply A; eassumption.
  - zify_cond G.
    assert (Hc : k_kind k = 0 \/ k_kind k = 1 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 4 \/
                 k_kind k = 5 \/ k_kind k = 6 \/ k_kind k = 7 \/ k_kind k = 8 \/ k_kind k = 9 \/
                 k_kind k = 10) by lia.
    clear G.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; rewrite H in A |- *;
      (match type of A with context [pc_run ?j] =>
         let v := eval vm_compute in (pc_run j) in change (pc_run j) with v in A end);
      do 7 step; eapply A; eassumption.
Qed.

(** ---- the segment ---- *)

Lemma codec_main_run : seg_run_stmt.
Proof.
  unfold seg_run_stmt. intros E n ENV C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 JOIN.
  pose proof (run_arm E n ENV C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 JOIN) as ARM.
  split; [exact (run_switch E n ENV ARM) | exact ARM].
Qed.
