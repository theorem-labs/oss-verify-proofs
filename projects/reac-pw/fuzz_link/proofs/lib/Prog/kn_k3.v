(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 294 of its 321 lines of code are new or changed and 295 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), part 3: the start of the operation. The errno
   table nl_errno.e (.rodata 0x106e4) read at a computed index, the failure masks of the flags byte, the four
   writes into g_nl (+0x12c .. +0x138), the chunk count n = byte % 4 and the spill slots (+0x164), then the
   first chunk (kn_k2.v k_first) or the epilogue. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  kn_k1 kn_k2.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The errno table and the masks
   ========================================================================== *)

Lemma nl_errno_tab_range : forall e, In e nl_errno_tab -> 1 <= e <= 111.
Proof.
  intros e H. cbn [nl_errno_tab In] in H. unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in H.
  lia.
Qed.

Lemma nl_errno_in : forall b, In (nl_errno b) nl_errno_tab.
Proof.
  intros b. unfold nl_errno. pose proof (Z.mod_pos_bound b 6 ltac:(lia)) as R.
  apply nth_In. cbn [length nl_errno_tab]. lia.
Qed.

(* a read of image bytes at a literal address *)
Ltac img_read :=
  match goal with
  | |- ov_read_bytes ?segs ?m ?a ?n = _ =>
      let E := addr_expr a in
      let Ez := zlit E in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          let obs := eval vm_compute in (image_bytes segs Ez n) in
          lazymatch obs with
          | Some ?bs =>
              let RO := fresh "ROimg" in
              assert (RO : ro_cells segs m Ez [CB n bs])
                by (apply (ro_cells_image segs m Ez bs HI); [vm_compute; reflexivity | lia | cbn; lia]);
              rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
                by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
              clear RO
          end
      end
  end.

Lemma errno_tab_rd : forall m ei, mem_inv rsegs m -> 0 <= ei < 6 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (67300 + Z.shiftl ei 2)) 4 = Some (le4 (wz (nl_errno ei))).
Proof.
  intros m ei MI H.
  assert (ei = 0 \/ ei = 1 \/ ei = 2 \/ ei = 3 \/ ei = 4 \/ ei = 5) as C by lia.
  destruct C as [->|[->|[->|[->|[->| ->]]]]];
  (match goal with |- ov_read_bytes _ _ (Z_to_bv 64 ?x) _ = _ => let v := eval vm_compute in x in change x with v end);
  img_read; vm_compute; reflexivity.
Qed.

(* a byte-wide identity in b, the goal `lhs = rhs`, checked over the 256 values *)
Ltac byte_fun_eq3 b BR :=
  lazymatch goal with |- ?l = ?r =>
    let f := lazymatch eval pattern b in l with ?f _ => f end in
    let g := lazymatch eval pattern b in r with ?g _ => g end in
    change (f b = g b); apply (by_enum256 f g); [vm_compute; reflexivity | exact BR]
  end.

Ltac errno_cases ER :=
  cbn [nl_errno_tab In] in ER; unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in ER;
  destruct ER as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].

(* the four writes of +0x12c .. +0x138 make g_nl's queue empty with the three errnos *)
Lemma skipn_upd_low : forall (bs : list byte) k l, (k + length l <= Z.to_nat 262676)%nat ->
  (Z.to_nat 262676 <= length bs)%nat ->
  skipn (Z.to_nat 262676) (upd_bytes bs k l) = skipn (Z.to_nat 262676) bs.
Proof.
  intros bs k l H1 H2. apply list_eq_nth. intros i. rewrite !nth_error_skipn.
  destruct (Nat.lt_ge_cases (Z.to_nat 262676 + i) (length bs)) as [Hi|Hi].
  - rewrite upd_bytes_nth by lia.
    match goal with |- context [if ?b then _ else _] => destruct b eqn:E end; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Nat.ltb_lt in E2. lia.
  - rewrite (proj2 (nth_error_None bs _)) by lia.
    apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.

Lemma kgnl_init : forall c kbs v1 v2 v3,
  Z.of_nat (length kbs) = 271992 -> skipn (Z.to_nat 262676) kbs = skipn (Z.to_nat 262676) (kf_kbs0 c) ->
  In v1 nl_errno_tab -> (v2 = 0 \/ In v2 nl_errno_tab) -> (v3 = 0 \/ In v3 nl_errno_tab) ->
  kgnl c (upd_bytes (upd_bytes (upd_bytes (upd_bytes kbs (Z.to_nat (466304 - 203648)) (le8 (Z_to_bv 64 0)))
            (Z.to_nat (466312 - 203648)) (le4 (Z_to_bv 64 v1))) (Z.to_nat (466316 - 203648)) (le4 (Z_to_bv 64 v2)))
            (Z.to_nat (466320 - 203648)) (le4 (Z_to_bv 64 v3))) 0.
Proof.
  intros c kbs v1 v2 v3 GL GS E1 E2 E3.
  pose proof (nl_errno_tab_range v1 E1) as R1.
  assert (R2 : 0 <= v2 <= 111) by (destruct E2 as [->|E2]; [lia | pose proof (nl_errno_tab_range v2 E2); lia]).
  assert (R3 : 0 <= v3 <= 111) by (destruct E3 as [->|E3]; [lia | pose proof (nl_errno_tab_range v3 E3); lia]).
  change (466304 - 203648) with 262656. change (466312 - 203648) with 262664.
  change (466316 - 203648) with 262668. change (466320 - 203648) with 262672.
  set (k1 := upd_bytes kbs (Z.to_nat 262656) (le8 (Z_to_bv 64 0))).
  assert (L1 : Z.of_nat (length k1) = 271992) by (unfold k1; rewrite upd_bytes_length by (rewrite length_le8; lia); exact GL).
  set (k2 := upd_bytes k1 (Z.to_nat 262664) (le4 (Z_to_bv 64 v1))).
  assert (L2 : Z.of_nat (length k2) = 271992) by (unfold k2; rewrite upd_bytes_length by (rewrite length_le4; lia); exact L1).
  set (k3 := upd_bytes k2 (Z.to_nat 262668) (le4 (Z_to_bv 64 v2))).
  assert (L3 : Z.of_nat (length k3) = 271992) by (unfold k3; rewrite upd_bytes_length by (rewrite length_le4; lia); exact L2).
  set (k4 := upd_bytes k3 (Z.to_nat 262672) (le4 (Z_to_bv 64 v3))).
  assert (L4 : Z.of_nat (length k4) = 271992) by (unfold k4; rewrite upd_bytes_length by (rewrite length_le4; lia); exact L3).
  assert (H4 : forall v, 0 <= v <= 111 -> rdn (le4 (Z_to_bv 64 v)) 0 4 = v).
  { intros v Hv. rewrite <- (app_nil_r (le4 (Z_to_bv 64 v))). rewrite rdn_le4_head by reflexivity.
    rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
  unfold kgnl. split; [unfold NK_SIZE; exact L4|].
  split.
  { unfold k4. rewrite skipn_upd_low by (rewrite ?length_le4; lia).
    unfold k3. rewrite skipn_upd_low by (rewrite ?length_le4; lia).
    unfold k2. rewrite skipn_upd_low by (rewrite ?length_le4; lia).
    unfold k1. rewrite skipn_upd_low by (rewrite ?length_le8; lia). exact GS. }
  split.
  { unfold k4. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k3. rewrite rdn_upd_out by (rewrite ?length_le4; lia).
    unfold k2. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k1. rewrite rdn_upd_in by (rewrite ?length_le8; lia).
    vm_compute. reflexivity. }
  split.
  { unfold k4. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k3. rewrite rdn_upd_out by (rewrite ?length_le4; lia).
    unfold k2. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k1. rewrite rdn_upd_in by (rewrite ?length_le8; lia).
    vm_compute. reflexivity. }
  split.
  { unfold k4. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k3. rewrite rdn_upd_out by (rewrite ?length_le4; lia).
    unfold k2. rewrite rdn_upd_in by (rewrite ?length_le4; lia).
    replace (262664 - Z.of_nat (Z.to_nat 262664)) with 0 by lia. rewrite H4 by lia. exact E1. }
  split.
  { unfold k4. rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k3. rewrite rdn_upd_in by (rewrite ?length_le4; lia).
    replace (262668 - Z.of_nat (Z.to_nat 262668)) with 0 by lia. rewrite H4 by lia. exact E2. }
  split.
  { unfold k4. rewrite rdn_upd_in by (rewrite ?length_le4; lia).
    replace (262672 - Z.of_nat (Z.to_nat 262672)) with 0 by lia. rewrite H4 by lia. exact E3. }
  intros i Hi. lia.
Qed.

(* the 32 spill bytes the prologue does not write, as the four words kspill names *)
Lemma cb32_c8 : forall m A pre post y,
  rw_cells rsegs m A (pre ++ CB 32 y :: post) ->
  exists w1 w2 w3 w4, rw_cells rsegs m A (pre ++ C8 w1 :: C8 w2 :: C8 w3 :: C8 w4 :: post).
Proof.
  intros m A pre post y C. pose proof C as [[Hwf _] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre Wy]. cbn [cells_wf cell_wf] in Wy. destruct Wy as [Ly Wpost].
  exists (Z_to_bv 64 (rdn y 0 8)), (Z_to_bv 64 (rdn y 8 8)), (Z_to_bv 64 (rdn y 16 8)), (Z_to_bv 64 (rdn y 24 8)).
  apply (rw_cells_same_bytes m A _ _ C).
  - apply cells_wf_app. split; [exact Wpre|]. cbn [cells_wf cell_wf]. repeat split; try exact I. exact Wpost.
  - assert (E : slice y 0 8 ++ slice y 8 8 ++ slice y 16 8 ++ slice y 24 8 = y).
    { pose proof (slice_full y) as SF. rewrite Ly in SF. change (Z.of_nat 32) with (8 + (8 + (8 + 8))) in SF.
      rewrite slice_split in SF by lia. rewrite slice_split in SF by lia. rewrite slice_split in SF by lia.
      exact SF. }
    rewrite !cells_bytes_app. f_equal. cbn [cells_bytes cbytes]. rewrite !app_assoc. f_equal.
    transitivity (slice y 0 8 ++ slice y 8 8 ++ slice y 16 8 ++ slice y 24 8); [|exact E].
    rewrite !(rdn_le8_slice y) by lia. rewrite !app_assoc. reflexivity.
  - rewrite !cells_size_app. cbn [cells_size csize]. lia.
Qed.

(* ==========================================================================
   2. The epilogue from any state of the walk
   ========================================================================== *)

Lemma k_exit_core : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la spl wbj wnc,
  rw_cells rsegs m (kSP c + -4336) spl -> cells_size spl = 120%nat ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) wnc -> cells_size wnc = 16%nat ->
  kcore c m adv kbs j la -> 0 <= j <= 3 ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14f6c) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 m adv kbs j la spl wbj wnc SPL LS WB WNC WNS KC JR.
  kctx c HC. kcore_unpack KC.
  eapply k_exit; [ | | | exact ST | exact SPL | exact LS | exact WB | exact WNC | exact WNS | exact FRS | ];
    [ lia | lia | lia | ].
  intros R' RP ST'.
  eapply (ko_fin c HC R' m kbs j adv la RP); [exact MU | exact WM | exact MI | exact ST' | exact NK | exact GI | lia
    | exact ADV | exact CUR | exact LA].
Qed.

Lemma k_f8 : forall c, kf_ok c -> k_msgloop_stmt ->
  forall (x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) m adv kbs la j1 j2 j3 j4 flags e ei,
  rw_cells rsegs m (kSP c + -104) (kfrs c) ->
  rw_cells rsegs m (kSP c + -120) [CB 16 j1] ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) j2] ->
  rw_cells rsegs m (kSP c + -4336) [CB 120 j3] ->
  0 <= adv <= kWN c ->
  rw_cells rsegs m (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] ->
  bytes_at rsegs m (kWP c) (kf_d c) ->
  u8arr rsegs m 203648 kbs -> Z.of_nat (length kbs) = 271992 ->
  skipn (Z.to_nat 262676) kbs = skipn (Z.to_nat 262676) (kf_kbs0 c) ->
  rw_cells rsegs m 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] ->
  munch (kW c) (kf_m0 c) m -> wmono rsegs (kf_m0 c) m -> mem_inv rsegs m ->
  stk rsegs m (kf_lo c) (kSP c + -4336) ->
  0 <= flags < 256 -> In e nl_errno_tab -> 0 <= ei < 6 ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (kf_s1 c)
             (Z_to_bv 64 67300) (Z_to_bv 64 e) (Z_to_bv 64 flags) (Z_to_bv 64 ei) j4 x15 x16 x17
             (kf_s2 c) (kf_s3 c) (kf_s4 c) (kf_s5 c) (kf_s6 c) (kf_s7 c) (kf_s8 c) (kf_s9 c) (kf_s10 c) (kf_s11 c)
             x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14288) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC KMS x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 m adv kbs la j1 j2 j3 j4 flags e ei FRS WNC WB SPL ADV CUR
    IN NK GL GS LA MU WM MI ST FR ER EIR.
  kctx c HC. unfold kfrs in FRS. unfold kW in MU.
  pose proof (nl_errno_tab_range e ER) as ERR. pose proof GL as GL0.
  do 10 zstep.
  pose proof (errno_tab_rd m ei MI EIR) as RDT.
  zstep. pose proof (nl_errno_tab_range _ (nl_errno_in ei)) as NER. rewrite sx32_wz by lia. unfold wz.
  repeat match goal with |- context [Z_to_bv 64 (Z.land ?s e)] =>
    first [ (lazymatch s with context [bv_signed _] => idtac end;
             replace (Z.land s e) with (if Z.odd flags then e else 0)
               by (clear - FR ER; errno_cases ER; byte_fun_eq3 flags FR))
          | replace (Z.land s e) with (if Z.testbit flags 1 then e else 0)
              by (clear - FR ER; errno_cases ER; byte_fun_eq3 flags FR) ] end.
  zstep. zstep.
  pose proof (u8arr_store_ok_z m 203648 kbs 466304 8 NK ltac:(lia) ltac:(lia)) as HS1.
  zstep. gnl_after_store NK GL.
  match goal with H : u8arr _ ?mm 203648 ?kb |- _ =>
    pose proof (u8arr_store_ok_z mm 203648 kb 466312 4 H ltac:(lia) ltac:(lia)) as HS2 end.
  zstep. gnl_after_store NK GL.
  match goal with H : u8arr _ ?mm 203648 ?kb |- _ =>
    pose proof (u8arr_store_ok_z mm 203648 kb 466316 4 H ltac:(lia) ltac:(lia)) as HS3 end.
  zstep. gnl_after_store NK GL.
  match goal with H : u8arr _ ?mm 203648 ?kb |- _ =>
    pose proof (u8arr_store_ok_z mm 203648 kb 466320 4 H ltac:(lia) ltac:(lia)) as HS4 end.
  zstep. gnl_after_store NK GL.
  assert (GI : kgnl c (upd_bytes (upd_bytes (upd_bytes (upd_bytes kbs (Z.to_nat (466304 - 203648))
            (le8 (Z_to_bv 64 0))) (Z.to_nat (466312 - 203648)) (le4 (Z_to_bv 64 (nl_errno ei))))
            (Z.to_nat (466316 - 203648)) (le4 (Z_to_bv 64 (if Z.odd flags then e else 0))))
            (Z.to_nat (466320 - 203648)) (le4 (Z_to_bv 64 (if Z.testbit flags 1 then e else 0)))) 0).
  { apply kgnl_init; [exact GL0 | exact GS | apply nl_errno_in | destruct (Z.odd flags); [right; exact ER | left; reflexivity]
      | destruct (Z.testbit flags 1); [right; exact ER | left; reflexivity]]. }
  clear GS GL0.
  zstep. zstep. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
  - (* no byte for n: the epilogue *)
    eapply k_exit_core with (j := 0) (adv := adv); [exact HC | exact SPL | reflexivity | exact WB | exact WNC | reflexivity
      | | lia].
    kcore_pack.
  - zstep. zstep. zstep. zstep. zstep.
    match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
      pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv) (Z_to_bv 64 (kWP c + adv)) H ltac:(lia) ltac:(lia)
                    eq_refl) as RD end.
    replace (kWP c + adv - kWP c) with adv in RD by lia.
    zstep. pose proof (rdn1_range (kf_d c) adv ltac:(lia) ltac:(lia)) as BR. rewrite zx8_wz by lia. unfold wz.
    zstep. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    + (* n = 0 chunks: the epilogue *)
      replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
      replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
      eapply k_exit_core with (j := 0) (adv := adv + 1); [exact HC | exact SPL | reflexivity | exact WB | exact WNC
        | reflexivity | | lia].
      kcore_pack.
    + do 28 zstep.
      assert (N4 : Z.land (rdn (kf_d c) adv 1) 3 = rdn (kf_d c) adv 1 mod 4).
      { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
      rewrite N4 in *. pose proof (Z.mod_pos_bound (rdn (kf_d c) adv 1) 4 ltac:(lia)) as NB.
      replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
      replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
      lazymatch goal with SPL : rw_cells _ ?mm (kSP c + -4336) (CB 16 ?x :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: CB 32 ?y :: ?post) |- _ =>
        destruct (cb32_c8 mm (kSP c + -4336) [CB 16 x; a1; a2; a3; a4; a5] post y SPL) as (w1 & w2 & w3 & w4 & SPL');
        clear SPL; rename SPL' into SPL; cbn [app] in SPL
      end.
      pose proof (k_first c HC KMS (rdn (kf_d c) adv 1 mod 4) ltac:(lia)) as KB0. unfold k_body_k in KB0.
      eapply KB0 with (adv := adv + 1) (j := 0); [exact SPL | exact WB | exact WNC | reflexivity | kcore_pack | lia].
Qed.

(* ==========================================================================
   4. The entry (+0x000 .. +0x0f4): the frame, the saved registers, and up to three input bytes
   ========================================================================== *)

Lemma k_entry : forall c, kf_ok c -> k_msgloop_stmt ->
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (kf_Q c)
    (MS (mkR (kf_ra c) (kf_sp c) (kf_gp c) (kf_tp c) t0 t1 t2 (kf_s0 c) (kf_s1 c) (kf_a0 c) a1 a2 a3 a4 a5 a6 a7
             (kf_s2 c) (kf_s3 c) (kf_s4 c) (kf_s5 c) (kf_s6 c) (kf_s7 c) (kf_s8 c) (kf_s9 c) (kf_s10 c) (kf_s11 c)
             t3 t4 t5 t6)
        (kf_F c) (Z_to_bv 64 0x14190) (kf_fc c) None (kf_m0 c) (seg_rom rsegs)).
Proof.
  intros c HC KMS t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  kctx c HC.
  pose proof (ko_st c HC) as ST. pose proof (ko_mi c HC) as MI.
  pose proof (ko_cu c HC) as CUR. pose proof (ko_in c HC) as IN. pose proof (ko_la c HC) as LA.
  pose proof (ko_nk c HC) as [NK GL]. unfold NK_SIZE in GL. change A_G_NL with 203648 in NK. pose proof (eq_refl (skipn (Z.to_nat 262676) (kf_kbs0 c))) as GS.
  pose proof (munch_refl (kW c) (kf_m0 c)) as MU. unfold kW in MU. pose proof (wmono_refl rsegs (kf_m0 c)) as WM.
  remember (kf_m0 c) as m eqn:Em.
  carve_z 104 ST. rename FR into FRS. change (Z.to_nat 104) with 104%nat in FRS.
  carve_z 16 ST. rename FR into WNC. change (Z.to_nat 16) with 16%nat in WNC.
  carve_z 4096 ST. rename FR into WB.
  carve_z 120 ST. rename FR into SPL. change (Z.to_nat 120) with 120%nat in SPL.
  zstep. do 13 zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  assert (EWP : kf_wp c = Z_to_bv 64 (kWP c)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  assert (EWN : kf_wn c = Z_to_bv 64 (kWN c)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  if_cases K0; zify_cond K0.
  - (* no input byte *)
    zstep. rewrite EWN.
    assert (CUR0 : rw_cells rsegs m0 (kCUR c) [C8 (Z_to_bv 64 (kWP c + 0)); C8 (Z_to_bv 64 (kWN c - 0))]).
    { rewrite Z.add_0_r, Z.sub_0_r, <- EWP, <- EWN. exact CUR. }
    rewrite Em in MU, WM.
    eapply k_f8 with (adv := 0) (flags := 0) (e := 105) (ei := kWN c); [exact HC | exact KMS | exact FRS | exact WNC
      | exact WB | exact SPL | lia | exact CUR0 | exact IN | exact NK | exact GL | exact GS | exact LA | exact MU
      | exact WM | exact MI | exact ST | lia | left; reflexivity | lia].
  - zstep. zstep. zstep. zstep. zstep.
    pose proof (bytes_at_rd1 _ (kWP c) (kf_d c) (kWP c + 0) (kf_wp c) IN ltac:(lia) ltac:(lia)
                  ltac:(unfold wa; rewrite Z.add_0_r; exact EWP)) as RD0.
    replace (kWP c + 0 - kWP c) with 0 in RD0 by lia.
    zstep. pose proof (rdn1_range (kf_d c) 0 ltac:(lia) ltac:(lia)) as BR0. rewrite zx8_wz by lia. unfold wz.
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    + (* one input byte *)
      zstep. zstep.
      replace (kWN c + -1) with (kWN c - 1) in * by lia.
      rewrite Em in MU, WM.
      eapply k_f8 with (adv := 1) (flags := rdn (kf_d c) 0 1) (e := 105) (ei := 0); [exact HC | exact KMS
        | exact FRS | exact WNC | exact WB | exact SPL | lia | exact CUR | exact IN | exact NK | exact GL | exact GS
        | exact LA | exact MU | exact WM | exact MI | exact ST | lia | left; reflexivity | lia].
    + zstep. zstep. zstep. zstep.
      match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
        pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + 1) _ H ltac:(lia) ltac:(lia) eq_refl) as RD1 end.
      replace (kWP c + 1 - kWP c) with 1 in RD1 by lia.
      zstep. pose proof (rdn1_range (kf_d c) 1 ltac:(lia) ltac:(lia)) as BR1. rewrite zx8_wz by lia. unfold wz.
      do 8 zstep.
      match goal with |- context [Z_to_bv 64 (Z.land ?x 255)] =>
        replace (Z.land x 255) with (rdn (kf_d c) 1 1 mod 6) by byte_fun_eq3 (rdn (kf_d c) 1 1) BR1 end.
      pose proof (Z.mod_pos_bound (rdn (kf_d c) 1 1) 6 ltac:(lia)) as M1.
      zstep. zstep.
      match goal with HI : mem_inv _ ?mm |- _ =>
        pose proof (errno_tab_rd mm (rdn (kf_d c) 1 1 mod 6) HI M1) as RDT end.
      zstep.
      pose proof (nl_errno_tab_range _ (nl_errno_in (rdn (kf_d c) 1 1 mod 6))) as NER. rewrite sx32_wz by lia. unfold wz.
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* two input bytes *)
        zstep. zstep.
        replace (kWN c + -2) with (kWN c - 2) in * by lia.
        rewrite Em in MU, WM.
        eapply k_f8 with (adv := 2) (flags := rdn (kf_d c) 0 1) (e := nl_errno (rdn (kf_d c) 1 1 mod 6)) (ei := 0);
          [exact HC | exact KMS | exact FRS | exact WNC | exact WB | exact SPL | lia | exact CUR | exact IN | exact NK
          | exact GL | exact GS | exact LA | exact MU | exact WM | exact MI | exact ST | lia | apply nl_errno_in | lia].
      * zstep. zstep. zstep. zstep.
        match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
          pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + 2) _ H ltac:(lia) ltac:(lia) eq_refl) as RD2 end.
        replace (kWP c + 2 - kWP c) with 2 in RD2 by lia.
        zstep. pose proof (rdn1_range (kf_d c) 2 ltac:(lia) ltac:(lia)) as BR2. rewrite zx8_wz by lia. unfold wz.
        do 7 zstep.
        match goal with |- context [Z_to_bv 64 (Z.land ?x 255)] =>
          replace (Z.land x 255) with (rdn (kf_d c) 2 1 mod 6) by byte_fun_eq3 (rdn (kf_d c) 2 1) BR2 end.
        pose proof (Z.mod_pos_bound (rdn (kf_d c) 2 1) 6 ltac:(lia)) as M2.
        zstep.
        replace (kWN c + -3) with (kWN c - 3) in * by lia.
        rewrite Em in MU, WM.
        eapply k_f8 with (adv := 3) (flags := rdn (kf_d c) 0 1) (e := nl_errno (rdn (kf_d c) 1 1 mod 6))
          (ei := rdn (kf_d c) 2 1 mod 6);
          [exact HC | exact KMS | exact FRS | exact WNC | exact WB | exact SPL | lia | exact CUR | exact IN | exact NK
          | exact GL | exact GS | exact LA | exact MU | exact WM | exact MI | exact ST | lia | apply nl_errno_in | lia].
Qed.
