(* the segment crt_m2 of check_round_trip in fuzz_frame.ubsan, 0x1333c .. 0x133c4 (crt_m2_ok : crt_m2_stmt). *)
(* The three tests of the answer of diginet_frame_build (0x1333c .. 0x13374, none of the aborts
   at 0x1334c, 0x13360, 0x13374 is taken), the call of spec_build_frame into want with zero_sum
   0 (0x13378 .. 0x133a8), then, when the answer is n, bcmp of out and want (0x133ac .. 0x133c0,
   the abort at 0x133c0 is not taken). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c memset_c
  bcmp_c diginet_frame_build_c spec_build_frame_c crt_defs crt_m2_lib.
Import ListNotations.
Open Scope Z_scope.

(** * Tactics of the walk *)

Ltac uns := rewrite ?unsigned_lit by lia.

(* Decide a branch whose condition holds by lia. *)
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* Decide a branch whose condition is a closed term. *)
Ltac brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* After a callee contract: its footprint with literal bounds, the transport of the facts, the
   return address. *)
Ltac m2_after mm MUc WMc MIc :=
  rewrite ?unsigned_lit in MUc by lia;
  lazymatch type of MUc with munch _ _ ?m' =>
    transport_after_call rsegs mm m' MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end;
    try clear mm end;
  rename MIc into m2MI;
  rewrite ?ret_pc_even by first [lia | reflexivity].

(** * 0x13378 .. 0x133c4: spec_build_frame into want, bcmp (out, want, n) when the answer is n *)

Lemma m2_tail : bcmp_contract -> spec_build_frame_contract ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                            (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] ->
    stk rsegs m want (want + n) ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    s4 = Z_to_bv 64 (build_code (fr_body b) n) ->
    s6 = Z_to_bv 64 (if crt_ok b then 0 else 1) ->
    evt rsegs (crt_m2_post sp gp tp s7 s8 s9 s10 s11 F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13378) fc None m (seg_rom rsegs)).
Proof.
  intros HBC HSB ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m w buf out want n b j sv HC HLB Hn LAY m2SW BB m2OUT STW STK Hsv m2FR m2MI E4 E6.
  subst s4 s6.
  destruct LAY as (Hbuf0 & Hbuf1 & Hout0 & Hout1 & Hwant0 & Hwant1 & Dow & Dob & Dwb & Hw0 & Hw1 & Hsp8).
  destruct (fr_code_ok b HC) as (L30 & ET & NB1 & NB2).
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLP).
  pose proof (length_fr_body b HC) as LFB.
  assert (LZ : Z.of_nat (length (fr_body b)) = fr_body_len b) by lia.
  assert (NL : n = Z.max 60 (30 + fr_body_len b)) by (subst n; unfold frame_len; lia).
  pose proof (u64_range sp) as Rsp.
  assert (RS : 0 <= fr_send b < 2^32) by exact (be32_range b 18).
  assert (RA : 0 <= fr_ack b < 2^32) by exact (be32_range b 22).
  assert (RR : 0 <= fr_retry b < 2^16) by exact (be16_range b 26).
  assert (RC : 0 <= fr_cmd b < 2^8) by exact (at8_range b 28).
  assert (RN : 0 <= fr_ncmds b < 2^8) by exact (at8_range b 29).
  assert (Ld : length (fr_dst b) = 6%nat) by (unfold fr_dst; rewrite length_firstn; lia).
  assert (Ls : length (fr_src b) = 6%nat) by (unfold fr_src; rewrite length_firstn, length_skipn; lia).
  assert (m2BD : bytes_at rsegs m buf (fr_dst b)).
  { pose proof (m2_bytes_sub m buf b 0 6 BB ltac:(lia)) as X. change (Z.of_nat 0) with 0 in X.
    rewrite Z.add_0_r in X. exact X. }
  pose proof (m2_bytes_sub m buf b 6 6 BB ltac:(lia)) as m2BS.
  change (Z.of_nat 6) with 6 in m2BS. change (firstn 6 (skipn 6 b)) with (fr_src b) in m2BS.
  pose proof (m2_bytes_sub m buf b 30 (Z.to_nat (fr_body_len b)) BB ltac:(lia)) as m2BY.
  change (Z.of_nat 30) with 30 in m2BY.
  change (firstn (Z.to_nat (fr_body_len b)) (skipn 30 b)) with (fr_body b) in m2BY.
  clear BB.
  unfold spec_cells in m2SW.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (want, want + n)] m) as m2MU.
  pose proof (wmono_refl rsegs m) as m2WM.
  (* want: n writable bytes *)
  destruct (stk_carve rsegs _ want (want + n) (Z.to_nat n) STW ltac:(lia)) as [_ [jw WJ]].
  replace (want + n - Z.of_nat (Z.to_nat n)) with want in WJ by lia.
  clear STW.
  pose proof (m2_cb_len _ _ _ _ WJ) as LJ. rewrite <- LJ in WJ.
  (* 0x13378 .. 0x133a4: the fields of w; s5 = n; a0 = want; t5 = 0 *)
  do 12 step.
  rewrite (m2_zx16 (fr_retry b)) by lia.
  rewrite (m2_zxb (fr_cmd b)) by lia. rewrite (m2_zxb (fr_ncmds b)) by lia.
  rewrite (unsigned_lit n) by lia. rewrite (m2_swrap n) by lia.
  rewrite <- LZ.
  (* 0x133a8: spec_build_frame (want, buf, buf + 6, send, ack, retry, cmd, ncmds, buf + 30,
     body_len, 0) *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HSB with (out := want) (dst := buf) (src := buf + 6) (body := buf + 30) (zs := 0)
                      (lo := bv_unsigned sp - 240) (send := fr_send b) (ack := fr_ack b)
                      (retry := fr_retry b) (cmd := fr_cmd b) (ncmds := fr_ncmds b)
                      (dmac := fr_dst b) (smac := fr_src b) (bb := fr_body b) (oj := jw);
      first [ assumption | (left; reflexivity) | (unfold SBF_STACK; rewrite ?LJ, ?Z2Nat.id by lia; lia) ]
    | intros ms1 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mA & -> &
                  MU1 & WM1 & MI1 & STK1 & RW1);
      unfold SBF_STACK in MU1; rewrite LJ, Z2Nat.id in MU1 by lia; rewrite LJ in RW1;
      change (0 =? 1) with false in RW1;
      clear m2BD m2BS m2BY m2SW;
      m2_after mm MU1 WM1 MI1 ]
  end.
  (* 0x133ac: bne s4, s5 *)
  assert (OKc : crt_ok b = true \/ crt_ok b = false) by (destruct (crt_ok b); auto).
  destruct OKc as [OK|OK].
  - (* the answer is n: bcmp (out, want, n) *)
    pose proof (m2_code_true b OK) as BCn. rewrite <- Hn in BCn. rewrite BCn.
    step. br false. do 4 step.
    pose proof m2OUT as OUT2.
    rewrite m2_build_out_eq in OUT2 by (rewrite repeat_length, Z2Nat.id by lia; exact BCn).
    change (0 =? 1) with false in OUT2.
    pose proof (m2_rw_bytes _ _ _ OUT2) as OB. cbn [cells_bytes cbytes] in OB. rewrite app_nil_r in OB.
    pose proof (m2_rw_bytes _ _ _ RW1) as WB. cbn [cells_bytes cbytes] in WB. rewrite app_nil_r in WB.
    clear OUT2.
    pose proof (length_build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                  (fr_cmd b) (fr_ncmds b) (fr_body b) false Ld Ls) as LB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HBC with (ls := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                                 (fr_cmd b) (fr_ncmds b) (fr_body b) false)
                        (rs := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                                 (fr_cmd b) (fr_ncmds b) (fr_body b) false) (v := 0);
        [ uns; exact OB | uns; exact WB | uns; apply m2_memcmp_self; lia | eassumption ]
      | intros ms5 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mE & -> &
                    MU5 & WM5 & MI5 & _ & _);
        clear OB WB;
        m2_after mm MU5 WM5 MI5 ]
    end.
    (* 0x133c0: bnez a0 *)
    step. brc.
    apply evt_done. unfold crt_m2_post. do 19 eexists. split; [reflexivity|].
    split; [exact m2MU|]. split; [exact m2WM|]. split; [exact m2MI|]. split; [exact m2FR|].
    split; [exact m2OUT|]. split; [exact RW1 | exact STK1].
  - (* the answer is -4 or -10: no bcmp *)
    destruct (m2_code_false b n OK) as [BCx|BCx]; rewrite BCx; step; br true;
    apply evt_done; unfold crt_m2_post; do 19 eexists;
    (split; [reflexivity|]);
    (split; [exact m2MU|]); (split; [exact m2WM|]); (split; [exact m2MI|]); (split; [exact m2FR|]);
    (split; [exact m2OUT|]); (split; [exact RW1 | exact STK1]).
Qed.

(** * 0x1333c .. 0x133c4 *)

Lemma crt_m2_ok : crt_m2_stmt.
Proof.
  unfold crt_m2_stmt.
  intros HBC HSB ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w buf out want n b j sv HC HLB Hn LAY SW BB OUT STW STK Hsv FR MI.
  pose proof (u64_range sp) as Rsp.
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLP).
  pose proof (length_fr_body b HC) as LFB.
  assert (NL : n = Z.max 60 (30 + Z.of_nat (length (fr_body b)))) by (subst n; unfold frame_len; lia).
  unfold crt_sys.
  destruct (Z.le_gt_cases (Z.of_nat (length (fr_body b))) 1484) as [FIT|NFIT];
    destruct (system_at (fr_body b)) eqn:SYS; cbv iota.
  (* 0x1333c .. 0x13374: the answer is -4 past 1484 body bytes, else -10 for a system
     message, else n; s6 = sys | !fits *)
  1: { (* fits, sys: -10 *)
    assert (BC : build_code (fr_body b) n = -10).
    { unfold build_code. rewrite SYS.
      replace (1484 <? Z.of_nat (length (fr_body b))) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity. }
    assert (OK : crt_ok b = false) by (unfold crt_ok; rewrite SYS; cbn [negb]; apply andb_false_r).
    rewrite BC.
    step. step. step. br true.
    step. rewrite m2_sltiu_t by lia.
    step. step. brc.
    step. step. brc.
    step. step. step. brc.
    eapply m2_tail; try eassumption.
    - rewrite BC. first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].
    - rewrite OK. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  1: { (* fits, no sys: n *)
    assert (OK : crt_ok b = true).
    { unfold crt_ok. rewrite SYS. apply andb_true_iff. split; [apply Z.leb_le; lia | reflexivity]. }
    pose proof (m2_code_true b OK) as BC. rewrite <- Hn in BC. rewrite BC.
    step. step. step. br true.
    step. rewrite m2_sltiu_t by lia.
    step. step. brc.
    step. step. step. brc.
    step. step.
    rewrite (unsigned_lit n) by lia. rewrite (m2_swrap n) by lia. br false.
    eapply m2_tail; try eassumption.
    - rewrite BC. first [reflexivity | f_equal; lia].
    - rewrite OK. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  (* past 1484 body bytes: -4 *)
  all: assert (BC : build_code (fr_body b) n = -4) by
         (unfold build_code;
          replace (1484 <? Z.of_nat (length (fr_body b))) with true by (symmetry; apply Z.ltb_lt; lia);
          reflexivity).
  all: assert (OK : crt_ok b = false) by
         (unfold crt_ok;
          replace (Z.of_nat (length (fr_body b)) <=? 1484) with false by (symmetry; apply Z.leb_gt; lia);
          reflexivity).
  all: rewrite BC.
  all: step; step; step; br false.
  all: step; step; brc.
  all: step; rewrite m2_sltiu_f by lia.
  all: step; step; brc.
  all: step; step; step; brc.
  all: eapply m2_tail; try eassumption.
  all: first [ rewrite BC; first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity]
             | rewrite OK; first [reflexivity | apply bv_eq; vm_compute; reflexivity] ].
Qed.
