From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import printf_facts_c snprintf_c memcpy_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import dcsv_lem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** The walk of reac_rate_drivable_csv (plain image, 0x14a78, 99 instructions), from snprintf_contract and
    memcpy_contract, in pieces: the entry (0x14a78 .. 0x14b00) carves the 176-byte frame, saves ra and s0-s11 at
    sp + 0x48 .. 0xaf, buf and buflen at sp + 8 and sp + 0x10, writes tmp[0] = 0 and loads the loop constants; one
    pass of the loop (0x14b04 .. 0x14b8c, [dc_pass]) reads ordered[i] from .rodata, runs the inlined reac_rate_bit
    compare chain and tests bit i of mask; a set bit ([dc_body], [dc_tail]) calls snprintf(cell, 16, "%s%d", sep,
    rate) ([dc_snp]), checks its result (both skip branches are dead: the list is at most 17 bytes), calls
    memcpy(tmp + len, cell, n) ([dc_mcp]) and stores the NUL at tmp[len + n]; the exit (0x14b90 .. 0x14c00,
    [dc_exit], [dc_exit_tail], [dc_mcp_exit], [dc_ret]) copies min(len, buflen - 1) bytes and a NUL to buf when
    buflen > 0, restores the registers and returns len. The loop state between passes is [dc_mem]: the frame cells,
    tmp holding csv_prefix mask i and its NUL, and the memory written only below the entry sp. *)

Lemma eqb0_lit : forall x, 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof. intros x Hx. unfold bv_eqb. rewrite (unsigned_lit x) by lia. reflexivity. Qed.

Lemma ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. rewrite bv_ltu_Z, (unsigned_lit x), (unsigned_lit y) by lia. reflexivity. Qed.

Lemma lts0_lit : forall x, 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.

Lemma land_pow : forall k mask, 0 <= k -> Z.land (2 ^ k) mask = if Z.testbit mask k then 2 ^ k else 0.
Proof.
  intros k mask Hk. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec.
  destruct (Z.eq_dec j k) as [->|Hne].
  - rewrite Z.pow2_bits_true by lia.
    destruct (Z.testbit mask k); [rewrite Z.pow2_bits_true by lia | rewrite Z.bits_0]; reflexivity.
  - rewrite Z.pow2_bits_false by lia.
    destruct (Z.testbit mask k); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.

(** The code's bit test (`and a0,a0,s3; beqz a0`, 0x14b30) on reac_rate_bit's answer 2^i. *)
Lemma bit_test : forall (i : nat) b mask, b = 2 ^ Z.of_nat i -> (i < 3)%nat -> 0 <= mask < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land b (bv_unsigned (Z_to_bv 64 mask)))) (Z_to_bv 64 0) = negb (Z.testbit mask (Z.of_nat i)).
Proof.
  intros i b mask -> Hi Hm. rewrite (unsigned_lit mask) by lia. rewrite land_pow by lia.
  assert (0 < 2 ^ Z.of_nat i <= 4).
  { split; [apply Z.pow_pos_nonneg; lia|]. apply Z.le_trans with (2 ^ 2); [apply Z.pow_le_mono_r; lia | lia]. }
  destruct (Z.testbit mask (Z.of_nat i)); rewrite eqb0_lit by lia; cbn [negb]; [apply Z.eqb_neq | apply Z.eqb_eq]; lia.
Qed.

Lemma prefix_set : forall mask i, Z.testbit mask (Z.of_nat i) = true ->
  csv_prefix mask (S i) = csv_prefix mask i ++ (match csv_prefix mask i with [] => [] | _ :: _ => [44] end) ++
                          csv_dec (nth i closed_list 0).
Proof. intros mask i H. rewrite csv_prefix_S, H. reflexivity. Qed.

Lemma prefix_clr : forall mask i, Z.testbit mask (Z.of_nat i) = false -> csv_prefix mask (S i) = csv_prefix mask i.
Proof. intros mask i H. rewrite csv_prefix_S, H. reflexivity. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:217-219 *)
Ltac fp_tac := unfold sub_fp; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [outside] in *;
  repeat split; try exact I; lia.
Ltac dj_tac := cbn [disjoint_from cells_size csize Nat.add];
  rewrite ?csv_bytes_length, ?length_pf_bytes, ?length_app, ?length_le8; cbn [length];
  repeat split; try exact I; lia.

(** A branch whose condition the context decides. *)
Ltac br := first [ if_true | if_false ].

(** `sb zero,0(rX)` at a symbolic address A (tmp + len + n in the loop, buf + copy at the exit), into the one-byte
    cell JN at A: the store's permission from JN, the step, then the cell update and the transports of
    Tac.mem_after_store. *)
Ltac nul_step JN :=
  lazymatch type of JN with rw_cells ?segs ?mm ?A [CB 1 ?j] =>
    let HS := fresh "HS" in
    assert (HS : store_ok segs mm (Z_to_bv 64 A) 1 = true)
      by (apply (rw_cells_store_ok_at segs mm A [CB 1 j] 0 (CB 1 j) 1 (Z_to_bv 64 A) JN);
          [reflexivity | reflexivity | unfold wa; f_equal; lia]);
    step; clear HS; rewrite le1_zero;
    lazymatch goal with |- context [write_to_mem mm (Z_to_bv 64 A) ?bs] =>
      replace (write_to_mem mm (Z_to_bv 64 A) bs) with (write_to_mem mm (wa (A + Z.of_nat 0)) bs)
        by (unfold wa; f_equal; f_equal; lia)
    end;
    mem_after_store
  end.

Section DC.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (m0 : word -> option byte)
  (lo S mask buf n : Z) (canary : word) (junk : list byte).

Hypothesis Hn : 0 <= n <= 23.
Hypothesis Hmask : 0 <= mask < 2^64.
Hypothesis Hbuf : 0 <= buf < 2^64.
Hypothesis HB : 0 < n -> 0 < buf /\ rw_cells rsegs m0 buf [CB (Z.to_nat n) junk] /\ (buf + n <= lo \/ S <= buf).
Hypothesis ST0 : stk rsegs m0 lo S.
Hypothesis HK : lo + 6112 <= S.
Hypothesis HIMG : 0x50878 <= lo.
Hypothesis HS63 : S < 2^63.
Hypothesis MI0 : mem_inv rsegs m0.
Hypothesis TK0 : MemNorm.task_mem rsegs m0.
Hypothesis GG0 : bytes_at rsegs m0 0x1ea28 (le8 (Z_to_bv 64 0x50010)).
Hypothesis GD0 : bytes_at rsegs m0 0x50010 (le8 canary).
Hypothesis SNP : snprintf_contract.
Hypothesis MCP : memcpy_contract.

Local Abbreviation sv := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(** The contract's post, with sp = Z_to_bv 64 S. *)
Definition dc_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length (csv_list mask))))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F0 k) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo S /\
    (n = 0 -> munch [(lo, S)] m0 m') /\
    (0 < n -> munch [(lo, S); (buf, buf + n)] m0 m' /\
              bytes_at rsegs m' buf (csv_bytes (csv_cut (csv_list mask) n ++ [0]))).

(** The frame (sp = S - 176): sp + 0 .. 0x17 (8 unused bytes, buf, buflen), the cell and tmp at sp + 0x18 .. 0x47
    (readable and writable), the saved registers at sp + 0x48 .. 0xaf; the stack below it; FP state. *)
Definition dc_fr (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  (exists j0, rw_cells rsegs m (S + -176) [CB 8 j0; C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 n)]) /\
  rw_cells rsegs m (S + -104) sv /\ stk rsegs m (S + -152) (S + -104) /\ stk rsegs m lo (S + -176) /\
  wmono rsegs m0 m /\ mem_inv rsegs m /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k).

(** At the loop head: tmp holds P and its NUL. *)
Definition dc_mem (P : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  dc_fr m F fc /\ munch [(lo, S)] m0 m /\ bytes_at rsegs m (S + -136) (csv_bytes (P ++ [0])).

(** After snprintf: the cell holds T and its NUL. *)
Definition dc_mid (P T : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  dc_fr m F fc /\ munch [(lo, S)] m0 m /\ bytes_at rsegs m (S + -136) (csv_bytes (P ++ [0])) /\
  bytes_at rsegs m (S + -152) (csv_bytes (T ++ [0])).

(** After memcpy: tmp holds P ++ T. *)
Definition dc_cp (P T : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  dc_fr m F fc /\ munch [(lo, S)] m0 m /\ bytes_at rsegs m (S + -136) (csv_bytes (P ++ T)).

(** The loop head (pc 0x14b04) and the loop test (0x14b8c) at pass i with len = |P_i|. *)
Definition dc_st (i : nat) (len pc : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) : machine_state :=
  MS (mkR y1 (Z_to_bv 64 (S + -176)) gp tp y5 y6 y7 (Z_to_bv 64 67204) (Z_to_bv 64 len) y10 y11 y12 y13 y14 y15 y16
          y17 y18 (Z_to_bv 64 mask) (Z_to_bv 64 66672) (Z_to_bv 64 48000) (Z_to_bv 64 (S + -136))
          (Z_to_bv 64 (67192 + 4 * Z.of_nat i)) (Z_to_bv 64 44100) (Z_to_bv 64 66419) (Z_to_bv 64 66350)
          (Z_to_bv 64 96000) y28 y29 y30 y31)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Lemma dc_task : forall m, munch [(lo, S)] m0 m -> MemNorm.task_mem rsegs m.
Proof.
  intros m MU. eapply task_mem_munch; [exact TK0 | exact MU |]. intros a HI.
  assert (HR : lo <= bv_unsigned a < S) by (cbn [outside] in HI; lia).
  rewrite <- (Z_to_bv_lit_self a). apply (stk_wview m0 lo S); [exact ST0 | exact HR].
Qed.

(** snprintf(cell, 16, "%s%d", sep, rate) at 0x14b50, returning to 0x14b54. *)
Lemma dc_snp : forall (P sep : list Z) (rate : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (Q : machine_state -> Prop)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  dc_mem P m F fc -> (rate = 44100 \/ rate = 48000 \/ rate = 96000) -> (length sep <= 1)%nat ->
  (length P + length sep + 5 <= 17)%nat ->
  pf_arg_ok m (S + -176) lo (S + -152) 16 x13 (APtr sep) ->
  x14 = Z_to_bv 64 rate -> x10 = Z_to_bv 64 (S + -152) -> x11 = Z_to_bv 64 16 -> x12 = Z_to_bv 64 66672 ->
  (forall (m1 : word -> option byte) (F1 : bvmap 5 word) (fc1 : bv 32)
          (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     dc_mid P (sep ++ csv_dec rate) m1 F1 fc1 ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x14b54) (Z_to_bv 64 (S + -176)) gp tp y5 y6 y7 x8 x9
                         (Z_to_bv 64 (Z.of_nat (length (sep ++ csv_dec rate)))) y11 y12 y13 y14 y15 y16 y17
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                    F1 (Z_to_bv 64 0x14b54) fc1 None m1 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x14b54) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x188a8) fc None m (seg_rom rsegs)).
Proof.
  intros P sep rate m F fc Q x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 DM HR HS HL AS E14 E10 E11 E12 K.
  subst x10 x11 x12 x14.
  destruct DM as (((j0 & FRa) & FRs & SC & ST & WM & MI & FC & FK) & MU & TMP).
  assert (LT : length (sep ++ csv_dec rate) = (length sep + 5)%nat)
    by (rewrite length_app; destruct HR as [->|[->| ->]]; reflexivity).
  assert (LD : length (csv_dec rate) = 5%nat) by (destruct HR as [->|[->| ->]]; reflexivity).
  assert (RR : 0 < rate < 2^31) by (destruct HR as [->|[->| ->]]; lia).
  destruct (stk_cb_at m (S + -152) (S + -104) (S + -152) 16 SC ltac:(lia) ltac:(lia)) as [jc JC].
  pose proof (SNP (Z_to_bv 64 0x14b54) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (S + -152))
                (Z_to_bv 64 16) (Z_to_bv 64 66672) x13 (Z_to_bv 64 rate) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                x26 x27 x28 x29 x30 x31 F fc m lo canary [37; 115; 37; 100] [Ps; Pd] [APtr sep; AInt rate]
                (sep ++ csv_dec rate) jc) as H.
  cbv zeta in H.
  rewrite (unsigned_lit (S + -176)), (unsigned_lit (S + -152)), (unsigned_lit 16), (unsigned_lit 66672) in H by lia.
  eapply evt_cut.
  { apply H; clear H.
    - apply fmt_sd_at. exact MI.
    - unfold RO_LO. lia.
    - unfold RO_END. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok]. split; [exact AS|]. split; [apply dc_int_arg; lia | exact I].
    - cbn [pf_text option_map]. rewrite app_nil_r, pf_dec_csv. reflexivity.
    - exact JC.
    - lia.
    - rewrite LT. lia.
    - lia.
    - right. lia.
    - apply img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FC.
    - exact MI.
    - apply dc_task. exact MU.
    - unfold GOT_GUARD, GUARD. eapply bytes_at_transport; [exact GG0 | exact MU | dj_tac].
    - unfold GUARD. eapply bytes_at_transport; [exact GD0 | exact MU | dj_tac]. }
  intros ms' PP. unfold printf_post in PP.
  destruct PP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Ft & fc' & m'
                  & E & MU' & WM' & MI' & TK' & FC' & FK' & ST' & BY').
  subst ms'.
  rewrite (ret_pc_even 0x14b54) by (lia || reflexivity).
  rewrite (unsigned_lit (S + -176)) in MU', ST' by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in MU', BY'.
  rewrite firstn_all2 in MU', BY' by lia.
  apply K.
  split; [|split; [|split]].
  - split; [exists j0; eapply rw_cells_transport; [exact FRa | exact MU' | exact WM' | dj_tac]|].
    split; [eapply rw_cells_transport; [exact FRs | exact MU' | exact WM' | dj_tac]|].
    split.
    { eapply stk_tr; [exact SC | exact MU' | exact WM' |]. intros x Hx.
      destruct (Z_lt_le_dec x (S + -152 + Z.of_nat (length (sep ++ csv_dec rate)) + 1)) as [X|X].
      - right. eapply bytes_at_mrd; [exact BY' | rewrite length_pf_bytes, length_app; cbn [length]; lia].
      - left. cbn [outside]. repeat split; try exact I; lia. }
    split; [exact ST'|]. split; [eapply wmono_trans; [exact WM | exact WM']|]. split; [exact MI'|].
    split; [exact FC'|]. intros k Hk. rewrite FK' by exact Hk. apply FK. exact Hk.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']; fp_tac].
  - eapply bytes_at_transport; [exact TMP | exact MU' | dj_tac].
  - exact BY'.
Qed.

(** memcpy(tmp + len, cell, n) at 0x14b70, returning to 0x14b74. *)
Lemma dc_mcp : forall (P T : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (Q : machine_state -> Prop)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  dc_mid P T m F fc -> (length P + length T <= 17)%nat -> (length T <= 6)%nat ->
  x10 = Z_to_bv 64 (S + -136 + Z.of_nat (length P)) -> x11 = Z_to_bv 64 (S + -152) ->
  x12 = Z_to_bv 64 (Z.of_nat (length T)) ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     dc_cp P T m' F fc ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x14b74) (Z_to_bv 64 (S + -176)) gp tp y5 y6 y7 x8 x9 x10 y11 y12 y13 y14 y15
                         y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                    F (Z_to_bv 64 0x14b74) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x14b74) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x1ce2c) fc None m (seg_rom rsegs)).
Proof.
  intros P T m F fc Q x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 MD HL HT E10 E11 E12 K.
  subst x10 x11 x12.
  destruct MD as (((j0 & FRa) & FRs & SC & ST & WM & MI & FC & FK) & MU & TMP & CEL).
  destruct (stk_cb_at m (S + -152) (S + -104) (S + -136 + Z.of_nat (length P)) (length T) SC ltac:(lia) ltac:(lia))
    as [jd JD].
  assert (CEL' : bytes_at rsegs m (S + -152) (csv_bytes T)).
  { rewrite csv_bytes_app in CEL. apply bytes_at_app in CEL. exact (proj1 CEL). }
  assert (TMP' : bytes_at rsegs m (S + -136) (csv_bytes P)).
  { rewrite csv_bytes_app in TMP. apply bytes_at_app in TMP. exact (proj1 TMP). }
  clear TMP CEL.
  eapply evt_cut.
  { eapply (MCP (Z_to_bv 64 0x14b74) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9
              (Z_to_bv 64 (S + -136 + Z.of_nat (length P))) (Z_to_bv 64 (S + -152)) (Z_to_bv 64 (Z.of_nat (length T)))
              x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m (csv_bytes T) jd).
    - rewrite unsigned_lit by lia. exact CEL'.
    - rewrite unsigned_lit by lia. rewrite csv_bytes_length. lia.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact JD.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU' & WM'
                  & MI' & RW' & BY').
  subst ms'.
  rewrite (ret_pc_even 0x14b74) by (lia || reflexivity).
  rewrite !unsigned_lit in MU', RW' by lia. rewrite Nat2Z.id in RW'.
  destruct (rwc_cb _ _ _ _ RW') as [_ BT].
  apply K.
  split; [|split].
  - split; [exists j0; eapply rw_cells_transport; [exact FRa | exact MU' | exact WM' | dj_tac]|].
    split; [eapply rw_cells_transport; [exact FRs | exact MU' | exact WM' | dj_tac]|].
    split.
    { eapply stk_tr; [exact SC | exact MU' | exact WM' |]. intros x Hx.
      destruct (Z_lt_le_dec x (S + -136 + Z.of_nat (length P))) as [X|X];
        [|destruct (Z_lt_le_dec x (S + -136 + Z.of_nat (length P) + Z.of_nat (length T))) as [Y|Y]].
      - left. cbn [outside]. repeat split; try exact I; lia.
      - right. eapply bytes_at_mrd; [exact BT | rewrite csv_bytes_length; lia].
      - left. cbn [outside]. repeat split; try exact I; lia. }
    split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | dj_tac]|].
    split; [eapply wmono_trans; [exact WM | exact WM']|]. split; [exact MI'|]. split; [exact FC|]. exact FK.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']; fp_tac].
  - rewrite csv_bytes_app. apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact TMP' | exact MU' | dj_tac].
    + rewrite csv_bytes_length. exact BT.
Qed.

(** A set bit, from `mv a3,s10`'s successor 0x14b44 (a3 = sep) to 0x14b88. *)
Lemma dc_tail : forall (P sep : list Z) (Asep rate : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (Q : machine_state -> Prop)
    (x1 x5 x6 x7 x8 x10 x11 x12 x15 x16 x17 x18 x19 x21 x23 x24 x27 x28 x29 x30 x31 : word),
  (rate = 44100 \/ rate = 48000 \/ rate = 96000) -> (length sep <= 1)%nat ->
  (length P + length sep + 5 <= 17)%nat -> dc_mem P m F fc ->
  pf_arg_ok m (S + -176) lo (S + -152) 16 (Z_to_bv 64 Asep) (APtr sep) ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 : word),
     dc_mem (P ++ sep ++ csv_dec rate) m' F' fc' ->
     evt rsegs Q (MS (mkR z1 (Z_to_bv 64 (S + -176)) gp tp z5 z6 z7 x8
                        (Z_to_bv 64 (Z.of_nat (length (P ++ sep ++ csv_dec rate))))
                        z10 z11 z12 z13 z14 z15 z16 z17 z18 x19 (Z_to_bv 64 66672) x21 (Z_to_bv 64 (S + -136)) x23 x24
                        (Z_to_bv 64 66419) (Z_to_bv 64 66350) x27 z28 z29 z30 z31)
                   F' (Z_to_bv 64 0x14b88) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length P)))
                     x10 x11 x12 (Z_to_bv 64 Asep) (Z_to_bv 64 rate) x15 x16 x17 x18 x19 (Z_to_bv 64 66672) x21
                     (Z_to_bv 64 (S + -136)) x23 x24 (Z_to_bv 64 66419) (Z_to_bv 64 66350) x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0x14b44) fc None m (seg_rom rsegs)).
Proof.
  intros P sep Asep rate m F fc Q x1 x5 x6 x7 x8 x10 x11 x12 x15 x16 x17 x18 x19 x21 x23 x24 x27 x28 x29 x30 x31
    HR HS HL DM AS K.
  assert (LT : length (sep ++ csv_dec rate) = (length sep + 5)%nat)
    by (rewrite length_app; destruct HR as [->|[->| ->]]; reflexivity).
  assert (LD : length (csv_dec rate) = 5%nat) by (destruct HR as [->|[->| ->]]; reflexivity).
  (* addi a0,sp,0x18; addi a1,zero,16; mv a2,s4; jal snprintf *)
  step. step. step. step.
  eapply dc_snp with (P := P) (sep := sep) (rate := rate);
    [ exact DM | exact HR | exact HS | exact HL | exact AS | reflexivity | first [reflexivity | f_equal; lia]
    | reflexivity | reflexivity | ].
  intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MD.
  (* bltz a0 (not taken); mv a2,a0; add s2,s1,a0; addi a0,zero,31; bltu a0,s2 (not taken) *)
  step. rewrite lts0_lit by lia. try br.
  step. step. step. step. rewrite ltu_lit by lia. if_false.
  (* add a0,s6,s1; addi a1,sp,0x18; jal memcpy *)
  step. step. step.
  eapply dc_mcp with (P := P) (T := sep ++ csv_dec rate);
    [ exact MD | lia | lia | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | reflexivity | ].
  intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 DC.
  destruct DC as (((j0 & FRa) & FRs & SC & ST & WM & MI & FC & FK) & MU & TM2).
  assert (LTM : length (csv_bytes (P ++ sep ++ csv_dec rate)) = (length P + length (sep ++ csv_dec rate))%nat)
    by (rewrite csv_bytes_length, length_app; reflexivity).
  (* add a0,s6,s2; sb zero,0(a0) *)
  step.
  destruct (stk_cb_at m2 (S + -152) (S + -104)
              (S + -136 + (Z.of_nat (length P) + Z.of_nat (length (sep ++ csv_dec rate)))) 1 SC ltac:(lia) ltac:(lia))
    as [jn JN].
  nul_step JN.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  assert (TM3 : bytes_at rsegs m3 (S + -136) (csv_bytes ((P ++ sep ++ csv_dec rate) ++ [0]))).
  { rewrite csv_bytes_app. apply bytes_at_app. split; [exact TM2|].
    destruct JN as [[_ JB] _]. cbn [cells_bytes cbytes app] in JB.
    rewrite LTM. replace (S + -136 + Z.of_nat (length P + length (sep ++ csv_dec rate)))
      with (S + -136 + (Z.of_nat (length P) + Z.of_nat (length (sep ++ csv_dec rate)))) by lia.
    exact JB. }
  (* j 8; mv s1,s2 *)
  step. step.
  replace (Z.of_nat (length P) + Z.of_nat (length (sep ++ csv_dec rate)))
    with (Z.of_nat (length (P ++ sep ++ csv_dec rate))) by (rewrite (length_app P); lia).
  eapply K.
  split; [|split; [exact MU | exact TM3]].
  split; [exists j0; exact FRa|]. split; [exact FRs|]. split; [exact SC|]. split; [exact ST|].
  split; [exact WM|]. split; [exact MI|]. split; [exact FC | exact FK].
Qed.

(** A set bit, from 0x14b38: `mv a3,s10; beqz s1` picks sep = "" for len = 0, else `mv a3,s9`: sep = ",". *)
Lemma dc_body : forall (P : list Z) (rate : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (Q : machine_state -> Prop)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x15 x16 x17 x18 x19 x21 x23 x24 x27 x28 x29 x30 x31 : word),
  (rate = 44100 \/ rate = 48000 \/ rate = 96000) ->
  (length (P ++ (match P with [] => [] | _ :: _ => [44%Z] end) ++ csv_dec rate) <= 17)%nat ->
  dc_mem P m F fc ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 : word),
     dc_mem (P ++ (match P with [] => [] | _ :: _ => [44] end) ++ csv_dec rate) m' F' fc' ->
     evt rsegs Q (MS (mkR z1 (Z_to_bv 64 (S + -176)) gp tp z5 z6 z7 x8
                        (Z_to_bv 64 (Z.of_nat (length (P ++ (match P with [] => [] | _ :: _ => [44] end) ++
                                                       csv_dec rate))))
                        z10 z11 z12 z13 z14 z15 z16 z17 z18 x19 (Z_to_bv 64 66672) x21 (Z_to_bv 64 (S + -136)) x23 x24
                        (Z_to_bv 64 66419) (Z_to_bv 64 66350) x27 z28 z29 z30 z31)
                   F' (Z_to_bv 64 0x14b88) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length P)))
                     x10 x11 x12 x13 (Z_to_bv 64 rate) x15 x16 x17 x18 x19 (Z_to_bv 64 66672) x21
                     (Z_to_bv 64 (S + -136)) x23 x24 (Z_to_bv 64 66419) (Z_to_bv 64 66350) x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0x14b38) fc None m (seg_rom rsegs)).
Proof.
  intros P rate m F fc Q x1 x5 x6 x7 x8 x10 x11 x12 x13 x15 x16 x17 x18 x19 x21 x23 x24 x27 x28 x29 x30 x31
    HR HL DM K.
  pose proof DM as ((_ & _ & _ & _ & _ & MI & _) & _ & _).
  assert (LD : length (csv_dec rate) = 5%nat) by (destruct HR as [->|[->| ->]]; reflexivity).
  rewrite !length_app in HL.
  step. step. rewrite eqb0_lit by lia.
  destruct P as [|p P'].
  - change (Z.of_nat (length (@nil Z)) =? 0) with true. cbv iota.
    eapply (dc_tail [] [] 66350 rate); [exact HR | cbn; lia | cbn [length] in HL |- *; lia | exact DM | | exact K].
    apply dc_s_empty; [exact MI | lia | lia].
  - replace (Z.of_nat (length (p :: P')) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
    cbv iota. step.
    eapply (dc_tail (p :: P') [44] 66419 rate); [exact HR | cbn; lia | cbn [length] in HL |- *; lia | exact DM | | exact K].
    apply dc_s_comma; [exact MI | lia | lia].
Qed.

(** One pass of the loop, 0x14b04 .. 0x14b8c, pass i = 0, 1, 2. *)
Lemma dc_pass : forall (i : nat) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
  (i < 3)%nat -> dc_mem (csv_prefix mask i) m F fc ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 : word),
     dc_mem (csv_prefix mask (Datatypes.S i)) m' F' fc' ->
     evt rsegs dc_post (dc_st (Datatypes.S i) (Z.of_nat (length (csv_prefix mask (Datatypes.S i)))) 0x14b8c F' fc' m'
                          z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31)) ->
  evt rsegs dc_post (dc_st i (Z.of_nat (length (csv_prefix mask i))) 0x14b04 F fc m
                       y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31).
Proof.
  intros i m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 Hi DM K.
  pose proof DM as ((_ & _ & _ & _ & _ & MI & _) & _ & _).
  pose proof (csv_prefix_length mask (Datatypes.S i) ltac:(lia) ltac:(lia)) as HLs.
  unfold dc_st.
  destruct i as [|[|[|i]]]; [| | | lia].
  - change (67192 + 4 * Z.of_nat 0) with 67192.
    step. step. br. step. step. step. step.
    rewrite (bit_test 0 1 mask) by (reflexivity || lia).
    destruct (Z.testbit mask (Z.of_nat 0)) eqn:EB; cbn [negb].
    + try br. rewrite (prefix_set mask 0 EB) in K, HLs.
      eapply (dc_body (csv_prefix mask 0) (nth 0 closed_list 0));
        [left; reflexivity | exact HLs
         | exact DM |].
      intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
      step. eapply K. exact DM'.
    + try br. rewrite (prefix_clr mask 0 EB) in K. step. eapply K. exact DM.
  - change (67192 + 4 * Z.of_nat 1) with 67196.
    step. step. br. step. br. step. br. step. step. step. step.
    rewrite (bit_test 1 2 mask) by (reflexivity || lia).
    destruct (Z.testbit mask (Z.of_nat 1)) eqn:EB; cbn [negb].
    + try br. rewrite (prefix_set mask 1 EB) in K, HLs.
      eapply (dc_body (csv_prefix mask 1) (nth 1 closed_list 0));
        [right; left; reflexivity | exact HLs
         | exact DM |].
      intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
      step. eapply K. exact DM'.
    + try br. rewrite (prefix_clr mask 1 EB) in K. step. eapply K. exact DM.
  - change (67192 + 4 * Z.of_nat 2) with 67200.
    step. step. br. step. br. step. step. step. step.
    rewrite (bit_test 2 4 mask) by (reflexivity || lia).
    destruct (Z.testbit mask (Z.of_nat 2)) eqn:EB; cbn [negb].
    + try br. rewrite (prefix_set mask 2 EB) in K, HLs.
      eapply (dc_body (csv_prefix mask 2) (nth 2 closed_list 0));
        [right; right; reflexivity | exact HLs
         | exact DM |].
      intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
      step. eapply K. exact DM'.
    + try br. rewrite (prefix_clr mask 2 EB) in K. step. eapply K. exact DM.
Qed.

Lemma bytes_at_firstn : forall m A bs k, bytes_at rsegs m A bs -> bytes_at rsegs m A (firstn k bs).
Proof. intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma csv_bytes_firstn : forall k l, csv_bytes (firstn k l) = firstn k (csv_bytes l).
Proof.
  unfold csv_bytes. induction k as [|k IH]; intros l; destruct l as [|x l]; cbn; try reflexivity.
  f_equal. apply IH.
Qed.

(** The epilogue from 0x14bc4: `mv a0,s1`, the restores of ra and s0-s11, `addi sp,sp,0xb0`, `ret`. *)
Lemma dc_ret : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  dc_fr m F fc ->
  (n = 0 -> munch [(lo, S)] m0 m) ->
  (0 < n -> munch [(lo, S); (buf, buf + n)] m0 m /\
            bytes_at rsegs m buf (csv_bytes (csv_cut (csv_list mask) n ++ [0]))) ->
  evt rsegs dc_post (MS (mkR x1 (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8
                           (Z_to_bv 64 (Z.of_nat (length (csv_list mask)))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x14bc4) fc None m (seg_rom rsegs)).
Proof.
  intros m F fc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 FRM R0 R1.
  destruct FRM as ((j0 & FRa) & FRs & SC & ST & WM & MI & FC & FK).
  assert (TK : MemNorm.task_mem rsegs m).
  { destruct (Z.eq_dec n 0) as [N0|N0]; [apply dc_task; exact (R0 N0)|].
    destruct (R1 ltac:(lia)) as [MU _]. destruct (HB ltac:(lia)) as (Hb0 & BUF & Hbl).
    eapply task_mem_munch; [exact TK0 | exact MU |]. intros a HI.
    rewrite <- (Z_to_bv_lit_self a).
    assert (HR : lo <= bv_unsigned a < S \/ buf <= bv_unsigned a < buf + n) by (cbn [outside] in HI; lia).
    destruct HR as [HR|HR].
    - apply (stk_wview m0 lo S); [exact ST0 | exact HR].
    - apply (rw_cells_wview m0 buf [CB (Z.to_nat n) junk]); [exact BUF | cbn [cells_size csize]; lia]. }
  assert (SC' : stk rsegs m (S + -152) (S + -152 + Z.of_nat 48)).
  { replace (S + -152 + Z.of_nat 48) with (S + -104) by lia. exact SC. }
  destruct (stk_cb m (S + -152) 48 SC') as [jm FRm].
  assert (FR : rw_cells rsegs m (S + -176) ([CB 8 j0; C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 n)] ++ [CB 48 jm] ++ sv)).
  { apply rw_cells_app. split; [exact FRa|]. apply rw_cells_app. cbn [cells_size csize Nat.add]. split.
    - replace (S + -176 + Z.of_nat 24) with (S + -152) by lia. exact FRm.
    - replace (S + -176 + Z.of_nat 24 + Z.of_nat 48) with (S + -104) by lia. exact FRs. }
  cbn [app] in FR. clear FRa FRs FRm SC SC'.
  do 15 step.
  step.
  release_frame FR ST S.
  replace (S + -176 + 176) with S by lia.
  finish.
Qed.

(** memcpy(buf, tmp, copy) at 0x14bb8, returning to 0x14bbc. *)
Lemma dc_mcp_exit : forall (copy : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (Q : machine_state -> Prop)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 < n -> copy = Z.min (Z.of_nat (length (csv_list mask))) (n - 1) -> dc_mem (csv_list mask) m F fc ->
  x10 = Z_to_bv 64 buf -> x11 = Z_to_bv 64 (S + -136) -> x12 = Z_to_bv 64 copy ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jn : list byte),
     dc_fr m' F fc -> munch [(lo, S); (buf, buf + n)] m0 m' ->
     bytes_at rsegs m' buf (csv_bytes (csv_cut (csv_list mask) n)) -> rw_cells rsegs m' (buf + copy) [CB 1 jn] ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x14bbc) (Z_to_bv 64 (S + -176)) gp tp y5 y6 y7 x8 x9 x10 y11 y12 y13 y14 y15
                         y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                    F (Z_to_bv 64 0x14bbc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x14bbc) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x1ce2c) fc None m (seg_rom rsegs)).
Proof.
  intros copy m F fc Q x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 Hn0 Hc DM E10 E11 E12 K.
  subst x10 x11 x12.
  destruct DM as (((j0 & FRa) & FRs & SC & ST & WM & MI & FC & FK) & MU & TMP).
  destruct (HB Hn0) as (Hb0 & BUF0 & Hbl).
  pose proof (csv_list_length mask ltac:(lia)) as HL.
  assert (Hc0 : 0 <= copy <= n - 1) by lia.
  assert (LC : length (csv_cut (csv_list mask) n) = Z.to_nat copy)
    by (rewrite csv_cut_length by lia; rewrite Hc; reflexivity).
  assert (BUF : rw_cells rsegs m buf [CB (Z.to_nat n) junk])
    by (eapply rw_cells_transport; [exact BUF0 | exact MU | exact WM | dj_tac]).
  pose proof (rwc_stk _ _ _ _ BUF) as SB. rewrite Z2Nat.id in SB by lia.
  destruct (stk_cb_at m buf (buf + n) buf (Z.to_nat copy) SB ltac:(lia) ltac:(lia)) as [jd JD].
  destruct (stk_cb_at m buf (buf + n) (buf + copy) 1 SB ltac:(lia) ltac:(lia)) as [jn JN].
  assert (SRC : bytes_at rsegs m (S + -136) (csv_bytes (csv_cut (csv_list mask) n))).
  { unfold csv_cut. rewrite csv_bytes_firstn. apply bytes_at_firstn.
    rewrite csv_bytes_app in TMP. apply bytes_at_app in TMP. exact (proj1 TMP). }
  eapply evt_cut.
  { eapply (MCP (Z_to_bv 64 0x14bbc) (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 x8 x9
              (Z_to_bv 64 buf) (Z_to_bv 64 (S + -136)) (Z_to_bv 64 copy)
              x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
              (csv_bytes (csv_cut (csv_list mask) n)) jd).
    - rewrite unsigned_lit by lia. exact SRC.
    - rewrite unsigned_lit by lia. rewrite csv_bytes_length. exact LC.
    - rewrite !unsigned_lit by lia. exact JD.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU' & WM'
                  & MI' & RW' & BY').
  subst ms'.
  rewrite (ret_pc_even 0x14bbc) by (lia || reflexivity).
  rewrite !unsigned_lit in MU', RW' by lia.
  destruct (rwc_cb _ _ _ _ RW') as [_ BT].
  apply (K m' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 jn).
  - split; [exists j0; eapply rw_cells_transport; [exact FRa | exact MU' | exact WM' | dj_tac]|].
    split; [eapply rw_cells_transport; [exact FRs | exact MU' | exact WM' | dj_tac]|].
    split; [eapply stk_transport_disjoint; [exact SC | exact MU' | exact WM' | dj_tac]|].
    split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | dj_tac]|].
    split; [eapply wmono_trans; [exact WM | exact WM']|]. split; [exact MI'|]. split; [exact FC|]. exact FK.
  - eapply munch_trans; [eapply munch_weaken; [|exact MU]; fp_tac | eapply munch_weaken; [|exact MU']; fp_tac].
  - exact BT.
  - eapply rw_cells_transport; [exact JN | exact MU' | exact WM' | dj_tac].
Qed.

(** The exit with buflen > 0 from 0x14ba8 (s0 = copy = min(len, buflen - 1)): memcpy, the NUL at buf + copy. *)
Lemma dc_exit_tail : forall (copy : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 < n -> copy = Z.min (Z.of_nat (length (csv_list mask))) (n - 1) -> dc_mem (csv_list mask) m F fc ->
  evt rsegs dc_post (MS (mkR x1 (Z_to_bv 64 (S + -176)) gp tp x5 x6 x7 (Z_to_bv 64 copy)
                           (Z_to_bv 64 (Z.of_nat (length (csv_list mask)))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x14ba8) fc None m (seg_rom rsegs)).
Proof.
  intros copy m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 Hn0 Hc DM.
  pose proof DM as (((j0 & FRa) & _) & _).
  destruct (HB Hn0) as (Hb0 & _ & Hbl).
  pose proof (csv_list_length mask ltac:(lia)) as HL.
  assert (Hc0 : 0 <= copy <= n - 1) by lia.
  (* addi a1,sp,0x28; ld s2,8(sp); mv a0,s2; mv a2,s0; jal memcpy *)
  step. step. step. step. step.
  eapply (dc_mcp_exit copy); [exact Hn0 | exact Hc | exact DM | reflexivity | first [reflexivity | f_equal; lia]
                             | reflexivity |].
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 jn FRM MU2 BYT JN.
  clear FRa DM.
  destruct FRM as ((j1 & FRa) & FRs & SC & ST & WM & MI & FC & FK).
  assert (LC : Z.of_nat (length (csv_bytes (csv_cut (csv_list mask) n))) = copy)
    by (rewrite csv_bytes_length, csv_cut_length by lia; lia).
  (* add s0,s2,s0; sb zero,0(s0) *)
  step.
  nul_step JN.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  assert (BY2 : bytes_at rsegs m2 buf (csv_bytes (csv_cut (csv_list mask) n ++ [0]))).
  { rewrite csv_bytes_app. apply bytes_at_app. split; [exact BYT|].
    destruct JN as [[_ JB] _]. cbn [cells_bytes cbytes app] in JB. rewrite LC. exact JB. }
  eapply dc_ret.
  - split; [exists j1; exact FRa|]. split; [exact FRs|]. split; [exact SC|]. split; [exact ST|].
    split; [exact WM|]. split; [exact MI|]. split; [exact FC | exact FK].
  - intros. lia.
  - intros _. split; [exact MU2 | exact BY2].
Qed.

(** The exit from 0x14b90: buflen = 0 returns len; else copy = min(len, buflen - 1) by the unsigned `bltu`. *)
Lemma dc_exit : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
  dc_mem (csv_prefix mask 3) m F fc ->
  evt rsegs dc_post (dc_st 3 (Z.of_nat (length (csv_prefix mask 3))) 0x14b90 F fc m
                       y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31).
Proof.
  intros m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 DM.
  pose proof DM as (((j0 & FRa) & _) & _).
  pose proof (csv_list_length mask ltac:(lia)) as HL. unfold csv_list in HL.
  unfold dc_st.
  (* ld a0,0x10(sp); beqz a0 *)
  step. step. rewrite eqb0_lit by lia.
  destruct (Z.eqb_spec n 0) as [N0|N0]; try br.
  - pose proof DM as (FRM & MU & _).
    eapply dc_ret; [exact FRM | intros _; exact MU | intros; lia].
  - (* addi a0,a0,-1; mv s0,s1; bltu s1,a0 *)
    step. step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (Z.of_nat (length (csv_prefix mask 3))) (n + -1)) as [C|C]; try br.
    + eapply (dc_exit_tail (Z.of_nat (length (csv_prefix mask 3)))); [lia | unfold csv_list; lia | exact DM].
    + step. eapply (dc_exit_tail (n + -1)); [lia | unfold csv_list; lia | exact DM].
Qed.

(** The loop: passes 2, 1, 0 and the loop test `bne s7,s0` at 0x14b8c. *)
Lemma dc_loop2 : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
  dc_mem (csv_prefix mask 2) m F fc ->
  evt rsegs dc_post (dc_st 2 (Z.of_nat (length (csv_prefix mask 2))) 0x14b04 F fc m
                       y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31).
Proof.
  intros m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 DM.
  eapply dc_pass; [lia | exact DM |].
  intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
  unfold dc_st. step. br. eapply dc_exit. exact DM'.
Qed.

Lemma dc_loop1 : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
  dc_mem (csv_prefix mask 1) m F fc ->
  evt rsegs dc_post (dc_st 1 (Z.of_nat (length (csv_prefix mask 1))) 0x14b04 F fc m
                       y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31).
Proof.
  intros m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 DM.
  eapply dc_pass; [lia | exact DM |].
  intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
  unfold dc_st. step. br. eapply dc_loop2. exact DM'.
Qed.

Lemma dc_loop0 : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
  dc_mem (csv_prefix mask 0) m F fc ->
  evt rsegs dc_post (dc_st 0 (Z.of_nat (length (csv_prefix mask 0))) 0x14b04 F fc m
                       y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31).
Proof.
  intros m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 DM.
  eapply dc_pass; [lia | exact DM |].
  intros m' F' fc' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31 DM'.
  unfold dc_st. step. br. eapply dc_loop1. exact DM'.
Qed.

(** The whole function from its entry 0x14a78. *)
Lemma dc_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  frm0 fc ->
  evt rsegs dc_post (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) (Z_to_bv 64 buf) (Z_to_bv 64 n)
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F0 (Z_to_bv 64 0x14a78) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc FC.
  pose proof ST0 as ST. pose proof MI0 as MI.
  set (mm := m0) in ST, MI |- *.
  assert (MU : munch [(lo, S)] m0 mm) by apply munch_refl.
  assert (WM : wmono rsegs m0 mm) by apply wmono_refl.
  carve_frame 176%nat ST.
  (* the saves, buf, buflen, s3 = mask, s1 = 0; `sb zero,0x28(sp)`; the constants *)
  do 19 step. rewrite le1_zero. mem_after_store. do 16 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm1 _) => rename mm1 into m1 end.
  lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
    destruct (proj1 (rw_cells_app m1 (S + -176) [c1; c2; c3] (c4 :: c5 :: c6 :: rest)) FR) as [FRa FRb];
    destruct (proj1 (rw_cells_app m1 _ [c4; c5; c6] rest) FRb) as [FRm FRs];
    destruct (proj1 (rw_cells_app m1 _ [c4] [c5; c6]) FRm) as [_ FR5];
    destruct (proj1 (rw_cells_app m1 _ [c5] [c6]) FR5) as [FR6 _]
  end.
  cbn [cells_size csize Nat.add] in FRm, FRs, FR6.
  pose proof (stk_of_rw_cells rsegs m1 _ _ FRm) as SC. cbn [cells_size csize Nat.add] in SC.
  destruct FR6 as [[_ B6] _]. cbn [cells_bytes cbytes app] in B6.
  eapply dc_loop0.
  split; [|split].
  - split; [eexists; exact FRa|].
    split; [replace (S + -104) with (S + -176 + Z.of_nat 24 + Z.of_nat 48) by lia; exact FRs|].
    split; [replace (S + -152) with (S + -176 + Z.of_nat 24) by lia;
            replace (S + -104) with (S + -176 + Z.of_nat 24 + Z.of_nat 48) by lia; exact SC|].
    split; [exact ST|]. split; [exact WM|]. split; [exact MI|]. split; [exact FC|]. intros; reflexivity.
  - exact MU.
  - replace (S + -136) with (S + -176 + Z.of_nat 24 + Z.of_nat 16) by lia. exact B6.
Qed.

End DC.
