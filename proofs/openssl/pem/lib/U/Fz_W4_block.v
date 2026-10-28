(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W4_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition dblock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (dl : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (T, T + 3 * (n0 / 4))] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4))
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ro_cells usegs m' C (ectx_cells num ed ln (Z_to_bv 64 0))
    /\ rw_cells usegs m' T [CB K bs'].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 48, bv_unsigned sp); (T, T + 3 * (n0 / 4))]%Z.
  Hypothesis AB : 0 <= n0 <= 80 /\ 3 * (n0 / 4) <= Z.of_nat K /\ 0 < C /\ C + 92 <= 2 ^ 64 /\ 0 < T /\ T + Z.of_nat K <= 2 ^ 64
                  /\ 0 <= lo /\ lo <= SP - 48 /\ SP < 2 ^ 64.
  Hypothesis CAL : C mod 4 = 0.
  Hypothesis SEP_CT : C + 92 <= T \/ T + Z.of_nat K <= C.
  Hypothesis SEP_CS : C + 92 <= lo \/ SP <= C.
  Hypothesis SEP_TS : T + Z.of_nat K <= lo \/ SP <= T.
  Hypothesis LED : length ed = 80%nat.

  Notation POST := (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition INV (mX : mem) : Prop :=
    ro_cells usegs mX C (ectx_cells num ed ln (Z_to_bv 64 0)) /\ bytes_at usegs mX (C + 4) ed
    /\ (exists bs, u8arr usegs mX T bs /\ length bs = K)
    /\ rw_cells usegs mX (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk usegs mX lo (SP + -48)
    /\ mem_inv usegs mX /\ munch W m mX /\ wmono usegs m mX.

  Ltac open_inv H := destruct H as (CTX & FB & (bs & DST & LBS) & FR & ST & MI & MU & WM).
  Ltac at_pc p :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => let d := eval vm_compute in (n =? p) in lazymatch d with true => idtac end
    end.
  Ltac closed_c c := match c with | context [?v] => is_var v; fail 1 | _ => idtac end.
  Ltac lit_br :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        closed_c c; let v := eval vm_compute in c in
        lazymatch v with true => change c with true; cbv iota | false => change c with false; cbv iota end
    end.
  Ltac dec_br :=
    let H := fresh "KB" in
    first [ if_cases H; zify_cond H; signed_lits_in H; rewrite ?unsigned_lit in H by lia; [exfalso; lia | clear H]
          | if_cases H; zify_cond H; signed_lits_in H; rewrite ?unsigned_lit in H by lia; [clear H | exfalso; lia] ].
  Ltac wst := first [ubs_if | lit_br | dec_br | zstep].
  Ltac go p := repeat (tryif at_pc p then fail else wst).

  Lemma inv_store_ok : forall mX k a, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> store_ok usegs mX a 1 = true.
  Proof.
    intros mX k a I Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n usegs mX T bs k 1 a DST); [lia | rewrite LBS; lia | exact Ha].
  Qed.

  Lemma inv_store : forall mX k a b, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> INV (write_to_mem mX a [b]).
  Proof.
    intros mX k a b I Hk Ha. pose proof (inv_store_ok mX k a I Hk Ha) as SOK. open_inv I. subst a.
    assert (HED : 0 <= C + 4 /\ C + 4 + Z.of_nat (length ed) <= 2 ^ 64) by (rewrite LED; lia).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply ro_cells_frame; [exact CTX | lia | cbn [length]; lia | cbn [length cells_size ectx_cells csize Nat.add]; lia].
    - apply bytes_at_write_other; [exact FB | lia | cbn [length]; lia | cbn [length]; rewrite LED; lia].
    - exists (upd_bytes bs (Z.to_nat k) [b]). split.
      + apply (u8arr_write_bytes usegs mX T bs k [b] DST); [lia | cbn [length]; rewrite LBS; lia].
      + rewrite upd_bytes_length; [exact LBS | cbn [length]; rewrite LBS; lia].
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. cbn [inside length]. right. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  Lemma ret_sx : forall dl, -1 <= dl <= 2 ^ 31 - 1 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 dl) + 0)) = Z_to_bv 64 dl.
  Proof.
    clear. intros dl H. destruct (Z.eq_dec dl (-1)) as [->|NE]; [reflexivity|].
    rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32).
    rewrite Z.add_0_r, Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma db_ret : forall mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4)) ->
    evt usegs POST (ST 0x1921fc mX x5 x6 x7 x9 (Z_to_bv 64 dl) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 I Hdl; open_inv I.
    do 9 ths.
    release_frame FR ST (bv_unsigned sp).
    rewrite ret_sx by lia. apply rw_cells_of_u8arr in DST. rewrite LBS in DST.
    apply evt_done. exists dl. do 14 eexists. exists bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Hdl|]. split; [exact ST|]. split; [exact CTX | exact DST].
  Qed.
  Lemma db_fail : forall mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX ->
    evt usegs POST (ST 0x1921f8 mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 I.
    zstep.
    eapply db_ret; [exact I | left; reflexivity].
  Qed.
  (* [comment removed for export] *)
  Ltac stb I k ADDR :=
    lazymatch type of I with INV ?mX =>
      let SOK := fresh "SOK" in
      pose proof (inv_store_ok mX k (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      rewrite t_le1_word;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?b]) _) =>
        let I2 := fresh "I" in
        pose proof (inv_store mX k (Z_to_bv 64 ADDR) b I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as I2;
        let m2 := fresh "m" in
        remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
        clear I; try clear mX; rename I2 into I
      end
    end.

  Lemma db_tail : forall mX k eofv x5 x6 x7 x9 x10 x13 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> 0 <= k -> k + 3 <= 3 * (n0 / 4) -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x192428 mX x5 x6 x7 x9 x10 (Z_to_bv 64 (T + k)) (Z_to_bv 64 k) x13 (Z_to_bv 64 eofv) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX k eofv x5 x6 x7 x9 x10 x13 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 I Hk0 Hk3 He.
    assert (SW : forall x, 0 <= x <= 2 ^ 31 - 1 -> bv_swrap 32 x = x).
    { clear. intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32).
      rewrite Z.mod_small by lia. lia. }
    assert (eofv = -1 \/ eofv = 0 \/ eofv = 1 \/ eofv = 2) as [-> | [-> | [-> | ->]]] by lia.
    1: repeat wst.
    1: repeat match goal with |- context [Z.b2z (?c <? 1)] => destruct (c <? 1) end.
    all: try change (Z.b2z true) with 1; try change (Z.b2z false) with 0.
    all: repeat (first [wst | stb I k (T + k) | stb I (k + 1) (T + k + 1) | stb I (k + 2) (T + k + 2)]).
    all: rewrite SW by lia; wst.
    all: eapply db_ret; [exact I | right; lia].
  Qed.

  Lemma db_ret0 : forall mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX ->
    evt usegs POST (ST 0x19236c mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 I.
    zstep. zstep.
    eapply db_ret; [exact I | right; lia].
  Qed.

  Ltac last_sgn NT :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if bv_lts (sxb ?b) (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
        let N := fresh "N" in let L := fresh "L" in let S := fresh "S" in let RB := fresh "RB" in
        let v := fresh "v" in let TR := fresh "TR" in
        pose proof (bv_unsigned_in_range 8 b) as RB; unfold bv_modulus in RB; change (2 ^ Z.of_N 8) with 256 in RB;
        destruct (sxb_cases b) as [[N L]|[N [L S]]]; rewrite N; cbv iota;
        [| rewrite S; destruct (NT b L) as [v TR]]
    end.
  Ltac last_go NT := repeat (tryif first [at_pc 0x1921f8 | at_pc 0x192428] then fail else first [last_sgn NT | wst]).
  Lemma db_last : forall mX k j eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> 0 <= k -> k + 4 <= n0 -> 0 <= j -> j + 3 <= 3 * (n0 / 4) -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x192378 mX x5 x6 x7 x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (T + j)) (Z_to_bv 64 j) x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + k)) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX k j eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31 I Hk0 Hk Hj0 Hj He.
    pose proof I as I0. open_inv I0. pose proof (b64_table_at mX MI) as TB.
    assert (NB : forall i, 0 <= i < 80 -> exists b, ov_read_bytes usegs mX (Z_to_bv 64 (C + 4 + i)) 1 = Some [b]).
    { intros i Hi. destruct (nth_error ed (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; rewrite LED in E; lia].
      exists b. apply (u8ro_read usegs mX (C + 4) ed i b); [exact FB | exact E | lia | unfold wa; f_equal; lia]. }
    assert (NT : forall b : byte, bv_unsigned b < 128 ->
                 exists v, ov_read_bytes usegs mX (Z_to_bv 64 (B64_TABLE + bv_unsigned b)) 1 = Some [v]).
    { intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. destruct (b64_table_nth (bv_unsigned b)) as [v Ev]; [lia|].
      exists v. apply (u8ro_read usegs mX B64_TABLE b64_table (bv_unsigned b) v); [exact TB | exact Ev | lia | reflexivity]. }
    destruct (NB k ltac:(lia)) as [b0 R0].
    destruct (NB (k + 1) ltac:(lia)) as [b1 R1].
    destruct (NB (k + 2) ltac:(lia)) as [b2 R2].
    destruct (NB (k + 3) ltac:(lia)) as [b3 R3].
    clear NB.
    last_go NT.
    all: try (let H := fresh "KF" in if_cases H; cbv iota).
    all: first [ eapply db_fail; exact I | eapply db_tail; [exact I | exact Hj0 | exact Hj | exact He] ].
  Qed.

  Lemma db_lexit : forall mX k j eofv w12 w30 w31 x5 x6 x7 x9 x11 x13 x16 x17 x18 x19 x20 x28 x29,
    INV mX -> 0 <= k -> k + 8 <= n0 -> 0 <= j -> j + 6 <= 3 * (n0 / 4) -> -1 <= eofv <= 2 ->
    w12 = Z_to_bv 64 (j + 3) -> w30 = Z_to_bv 64 (T + j) -> w31 = Z_to_bv 64 (C + 4 + k) ->
    evt usegs POST (ST 0x192360 mX x5 x6 x7 x9 (Z_to_bv 64 B64_TABLE) x11 w12 x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) x16 x17 x18 x19 x20 x28 x29 w30 w31).
  Proof.
    intros mX k j eofv w12 w30 w31 x5 x6 x7 x9 x11 x13 x16 x17 x18 x19 x20 x28 x29 I Hk0 Hk Hj0 Hj Heof -> -> ->.
    go 0x192378.
    replace (T + j + 3) with (T + (j + 3)) by lia. replace (C + 4 + k + 4) with (C + 4 + (k + 4)) by lia.
    apply db_last; [exact I | lia ..].
  Qed.

  Lemma db_sh_lts : forall L, 0 <= L < 256 -> bv_lts (Z_to_bv 64 (Z.shiftl L 56)) (Z_to_bv 64 0) = Z.testbit L 7.
  Proof.
    clear. intros L HL. pose proof (Z.testbit_spec' L 7 ltac:(lia)) as E. change (2 ^ 7) with 128 in E.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite bv_lts_zero_r, unsigned_lit by lia.
    destruct (Z.ltb_spec L 128).
    - rewrite (Z.div_small L 128) in E by lia. destruct (Z.testbit L 7); [discriminate|]. apply Z.leb_gt. lia.
    - assert (L / 128 = 1) as D by (Z.div_mod_to_equations; lia). rewrite D in E.
      destruct (Z.testbit L 7); [|discriminate]. apply Z.leb_le. lia.
  Qed.

  Lemma db_swrap32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
  Proof.
    clear. intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). lia.
  Qed.

  Local Ltac db_gw p := go p; repeat (rewrite db_swrap32 by lia; go p).

  Local Ltac db_lk b MI :=
    repeat wst;
    let SB := fresh "SB" in let HB := fresh "HB" in let EQ := fresh "EQ" in let Rb := fresh "Rb" in
    pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; change (2 ^ Z.of_N 8) with 256 in Rb;
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota;
    [ idtac
    | rewrite ?EQ;
      let v := fresh "v" in let Hv := fresh "Hv" in let Rv := fresh "Rv" in let RT := fresh "RT" in
      destruct (b64_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv];
      pose proof (bv_unsigned_in_range 8 v) as Rv; unfold bv_modulus in Rv; change (2 ^ Z.of_N 8) with 256 in Rv;
      pose proof (u8ro_read usegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b)) (b64_table_at _ MI) Hv ltac:(lia) eq_refl) as RT ].

  Local Ltac db_any I :=
    go 0x1921f8;
    first
      [ at_pc 0x1921f8
      | rewrite db_sh_lts by (change 256 with (2 ^ 8); repeat apply Z_lor_lt_pow2; lia);
        rewrite ?Z.lor_spec;
        repeat match goal with |- context [Z.testbit (bv_unsigned ?v) 7] => destruct (Z.testbit (bv_unsigned v) 7) end;
        go 0x1921f8 ];
    first [ at_pc 0x1921f8; apply db_fail; exact I | idtac ].

  Lemma db_loop_gen : forall r mX k n g eofv w6 w11 w16 w17 w28 w29 x9 x12 x18 x19 x20 x30 x31,
    n - 4 - 4 * g = 4 * Z.of_nat (S r) -> INV mX -> 0 <= k -> k + n <= n0 -> -1 <= eofv <= 2 -> 0 <= g ->
    w6 = Z_to_bv 64 (3 * g) -> w11 = Z_to_bv 64 (T + 3 * g) -> w16 = Z_to_bv 64 (C + 4 + k + 4 * g) ->
    w17 = Z_to_bv 64 (4 * g) -> w28 = Z_to_bv 64 (C + 4 + k + 4 * g) -> w29 = Z_to_bv 64 (T + 3 * g) ->
    evt usegs POST (ST 0x19224c mX (Z_to_bv 64 2) w6 (Z_to_bv 64 (2 ^ 64 - 1)) x9 (Z_to_bv 64 B64_TABLE) w11 x12
                       (Z_to_bv 64 (n + -4)) (Z_to_bv 64 eofv) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) w16 w17 x18 x19 x20 w28 w29 x30 x31).
  Proof.
    induction r as [r IH] using lt_wf_ind;
      intros mX k n g eofv w6 w11 w16 w17 w28 w29 x9 x12 x18 x19 x20 x30 x31 HR I Hk0 Hkn Heof Hg -> -> -> -> -> ->.
    rewrite Nat2Z.inj_succ in HR.
    assert (Hq : 3 * g + 3 <= 3 * (n0 / 4)) by (Z.div_mod_to_equations; lia).
    pose proof I as I0. open_inv I0.
    destruct (nth_error ed (Z.to_nat (k + 4 * g))) as [b0|] eqn:E0; [| apply nth_error_None in E0; lia].
    destruct (nth_error ed (Z.to_nat (k + 4 * g + 1))) as [b1|] eqn:E1; [| apply nth_error_None in E1; lia].
    destruct (nth_error ed (Z.to_nat (k + 4 * g + 2))) as [b2|] eqn:E2; [| apply nth_error_None in E2; lia].
    destruct (nth_error ed (Z.to_nat (k + 4 * g + 3))) as [b3|] eqn:E3; [| apply nth_error_None in E3; lia].
    pose proof (u8ro_read usegs mX (C + 4) ed _ b0 (Z_to_bv 64 (C + 4 + k + 4 * g)) FB E0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    pose proof (u8ro_read usegs mX (C + 4) ed _ b1 (Z_to_bv 64 (C + 4 + k + 4 * g + 1)) FB E1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R1.
    pose proof (u8ro_read usegs mX (C + 4) ed _ b2 (Z_to_bv 64 (C + 4 + k + 4 * g + 2)) FB E2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R2.
    pose proof (u8ro_read usegs mX (C + 4) ed _ b3 (Z_to_bv 64 (C + 4 + k + 4 * g + 3)) FB E3 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R3.
    db_lk b0 MI; db_lk b1 MI; db_lk b2 MI; db_lk b3 MI.
    all: db_any I.
    repeat wst. stb I (3 * g) (T + 3 * g).
    repeat wst. stb I (3 * g + 1) (T + 3 * g + 1).
    repeat wst. stb I (3 * g + 2) (T + 3 * g + 2).
    destruct r as [|r].
    - db_gw 0x192360.
      eapply (db_lexit _ (k + 4 * g) (3 * g) eofv); first [exact I | lia | (Z.div_mod_to_equations; lia) | (f_equal; lia)].
    - db_gw 0x19224c.
      eapply (IH r ltac:(lia) _ k n (g + 1) eofv); first [exact I | lia | (f_equal; lia)].
  Qed.

  Lemma db_loop : forall mX k n eofv x9 x12 x18 x19 x20 x30 x31,
    INV mX -> 0 <= k -> 4 < n -> k + n <= n0 -> n mod 4 = 0 -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x19224c mX (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 64 - 1)) x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) x12
                       (Z_to_bv 64 (n + -4)) (Z_to_bv 64 eofv) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + k)) (Z_to_bv 64 0)
                       x18 x19 x20 (Z_to_bv 64 (C + 4 + k)) (Z_to_bv 64 T) x30 x31).
  Proof.
    intros mX k n eofv x9 x12 x18 x19 x20 x30 x31 I Hk0 Hn4 Hkn Hn Heof.
    assert (Hr : n - 4 - 4 * 0 = 4 * Z.of_nat (S (Z.to_nat ((n - 8) / 4)))).
    { rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
    eapply (db_loop_gen _ mX k n 0 eofv); first [exact Hr | exact I | lia | (f_equal; lia)].
  Qed.

  Lemma db_pre : forall mX k n eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> 0 <= k -> 0 <= n -> k + n <= n0 -> n mod 4 = 0 -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x192220 mX x5 x6 x7 x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) (Z_to_bv 64 n) x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + k)) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX k n eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31 I Hk Hn Hkn Hm He.
    do 2 zstep. rewrite Z.add_0_r.
    replace (bv_swrap 32 n) with n by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
      change (2 ^ Z.of_N 32) with (2 ^ 32); change (2 ^ 32 `div` 2) with (2 ^ 31); rewrite Z.mod_small by lia; lia).
    if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    - go 0x19236c. eapply db_ret0; exact I.
    - zstep.
      replace (bv_swrap 32 (n + -4)) with (n + -4) by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
        change (2 ^ Z.of_N 32) with (2 ^ 32); change (2 ^ 32 `div` 2) with (2 ^ 31); rewrite Z.mod_small by lia; lia).
      repeat wst.
      destruct (Z.eq_dec n 4) as [E4|N4].
      + subst n. go 0x192378. replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 0)) by (f_equal; lia).
        eapply db_last; [exact I | lia | lia | lia | lia | exact He].
      + replace (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 (n + -4))) with true
          by (symmetry; unfold bv_lts; rewrite !signed_of_Z by lia; apply Z.ltb_lt; lia).
        go 0x19224c. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2 ^ 64 - 1)) by (apply bv_eq; reflexivity).
        eapply db_loop; [exact I | lia | lia | lia | exact Hm | exact He].
  Qed.

  Lemma db_chk : forall mX k n eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> 0 <= k -> 0 <= n -> k + n <= n0 -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x1921f0 mX x5 x6 x7 x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) (Z_to_bv 64 n) x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + k)) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX k n eofv x5 x6 x7 x9 x13 x17 x18 x19 x20 x28 x29 x30 x31 I Hk Hn Hkn He.
    do 2 zstep.
    replace (Z.land n 3) with (n mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
    - eapply db_pre; [exact I | exact Hk | exact Hn | exact Hkn | lia | exact He].
    - go 0x1921f8. eapply db_fail; exact I.
  Qed.

  Ltac tt_ltb := repeat match goal with |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia] end.
  Ltac tt_go p := repeat (tryif at_pc p then fail else first [wst | progress tt_ltb]).

  Lemma db_tt : forall (k : nat) mX nn j0 eofv p w x9 x18 x19 x20 x29 x31,
    INV mX -> Z.to_nat nn = k -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    p = C + 4 + j0 + nn - 1 -> w = Z.min nn 3 ->
    evt usegs POST (ST 0x19219c mX (Z_to_bv 64 p) (Z_to_bv 64 1) (Z_to_bv 64 224) x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) (Z_to_bv 64 w)
                       (Z_to_bv 64 nn) (Z_to_bv 64 eofv) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 4)
                       x18 x19 x20 (Z_to_bv 64 p) x29 (Z_to_bv 64 nn) x31).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX nn j0 eofv p w x9 x18 x19 x20 x29 x31 I HK Hnn Hj0 Hj He Hp Hw.
    zstep. if_cases K4; zify_cond K4; signed_lits_in K4.
    - go 0x1921f0. eapply (db_chk mX j0 w eofv); first [exact I | lia].
    - destruct (nth_error ed (Z.to_nat (j0 + nn - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
      pose proof (u8ro_read usegs _ (C + 4) ed (j0 + nn - 1) b (Z_to_bv 64 p) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      tt_go 0x19219c. clear RD.
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
      + go 0x1921f0. eapply (db_chk mX j0 nn eofv); first [exact I | lia].
      + rewrite EQ.
        destruct (b64_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv].
        pose proof (u8ro_read usegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                      (b64_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2.
        tt_go 0x19219c. clear RD2.
        if_cases KT.
        * tt_go 0x19219c.
          assert (SW : bv_swrap 32 (nn + -1) = nn + -1).
          { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
            rewrite Z.mod_small by lia. lia. }
          rewrite SW.
          eapply (IH (Z.to_nat (nn - 1))); first [exact I | lia].
        * go 0x1921f0. eapply (db_chk mX j0 nn eofv); first [exact I | lia].
  Qed.

  Lemma db_tt_entry : forall mX i eofv x5 x6 x7 x9 x17 x18 x19 x20 x28 x29 x30 x31,
    INV mX -> 0 <= i <= n0 -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x19216c mX x5 x6 x7 x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + i)) (Z_to_bv 64 (n0 - i))
                       (Z_to_bv 64 eofv) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + i)) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mX i eofv x5 x6 x7 x9 x17 x18 x19 x20 x28 x29 x30 x31 I Hi He.
    assert (L32 : Z.land (n0 - i) 4294967295 = n0 - i)
      by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    go 0x19219c. if_cases KN; zify_cond KN; signed_lits_in KN.
    - go 0x19219c. rewrite !L32. tt_ltb.
      eapply (db_tt (Z.to_nat (n0 - i)) mX (n0 - i) i eofv); first [exact I | reflexivity | lia].
    - go 0x19219c. rewrite !L32. tt_ltb.
      eapply (db_tt (Z.to_nat (n0 - i)) mX (n0 - i) i eofv); first [exact I | reflexivity | lia].
  Qed.

  Lemma db_ws : forall k mX i eofv x7 x9 x18 x19 x20 x28 x29 x30 x31,
    n0 - i = Z.of_nat k -> INV mX -> 0 <= i < n0 -> -1 <= eofv <= 2 ->
    evt usegs POST (ST 0x192124 mX (Z_to_bv 64 (-1)) (Z_to_bv 64 1) x7 x9 (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + i))
                       (Z_to_bv 64 (n0 - i)) (Z_to_bv 64 eofv) (Z_to_bv 64 (2 ^ 64 - 1 - B64_TABLE)) (Z_to_bv 64 (C + 4 + n0)) (Z_to_bv 64 224)
                       x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction k as [|k IH]; intros mX i eofv x7 x9 x18 x19 x20 x28 x29 x30 x31 EK I Hi He; [lia|].
    pose proof I as I0. open_inv I0.
    destruct (nth_error ed (Z.to_nat i)) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
    pose proof (u8ro_read usegs _ (C + 4) ed i b (Z_to_bv 64 (C + 4 + i)) FB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    destruct (sxb_cases b) as [(SN & B128) | (SN & B128 & SX)].
    - go 0x19216c. eapply (db_tt_entry mX i eofv); [exact I | lia | lia].
    - go 0x19216c. rewrite SX.
      pose proof (b64_table_at mX MI) as TB.
      assert (B0 : 0 <= bv_unsigned b) by (pose proof (bv_unsigned_in_range 8 b) as R8; lia).
      destruct (b64_table_nth (bv_unsigned b) ltac:(lia)) as (v & Hv).
      pose proof (u8ro_read usegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b)) TB Hv ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDT.
      destruct (Z.eq_dec (bv_unsigned v) 224) as [V224 | VN].
      2: { go 0x19216c. eapply (db_tt_entry mX i eofv); [exact I | lia | lia]. }
      destruct (Z.ltb_spec 1 (n0 - i)) as [L1 | L1].
      + go 0x192124.
        assert (SWE : bv_swrap 32 (n0 - i + -1) = n0 - (i + 1)).
        { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32).
          rewrite Z.mod_small by lia. lia. }
        rewrite SWE. clear SWE.
        replace (n0 - i + -1) with (n0 - (i + 1)) by lia.
        try replace (C + 4 + i + 1) with (C + 4 + (i + 1)) by lia.
        eapply (IH mX (i + 1) eofv); [lia | exact I | lia | lia].
      + go 0x19216c.
        try (assert (SWE : bv_swrap 32 (n0 - i + -1) = n0 - n0)
               by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31);
                   change (2 ^ Z.of_N 32) with (2 ^ 32); rewrite Z.mod_small by lia; lia);
             rewrite SWE; clear SWE).
        try replace (Z_to_bv 64 0) with (Z_to_bv 64 (n0 - n0)) by (f_equal; lia).
        replace (C + 4 + i + 1) with (C + 4 + n0) by lia.
        eapply (db_tt_entry mX n0 eofv); [exact I | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dblock_body : forall bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    ro_cells usegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> rw_cells usegs m T [CB K bs0] -> stk usegs m lo SP -> mem_inv usegs m ->
    -1 <= eofv <= 2 ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n0) (Z_to_bv 64 eofv) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1920c0) fc None m (seg_rom usegs)).
  Proof using All.
    intros bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 CTX DST ST MI He.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_cells_CB_length usegs _ _ _ _ DST) as LBS. apply u8arr_of_rw_cells in DST.
    pose proof (ectx_data m C num ed ln _ LED CTX) as FB.
    pose proof CTX as CTXb.
    apply (ro_cells_congr usegs m C _ [C4 num; CB 80 ed; C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CTXb;
      [| reflexivity | cbn; rewrite LED; tauto].
    unfold ectx_cells in CTX.
    th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
    go 0x192110. zstep.
    if_cases KN; zify_cond KN; signed_lits_in KN.
    - go 0x19216c.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - 0)) by (f_equal; lia).
      eapply (db_tt_entry _ 0 eofv); [| lia | lia].
      unfold INV. refine (conj CTX (conj FB (conj (ex_intro _ bs0 (conj DST LBS)) (conj FR (conj ST (conj MI (conj MU WM))))))).
    - go 0x192124.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - 0)) by (f_equal; lia).
      eapply (db_ws (Z.to_nat n0) _ 0 eofv); [lia | | lia | lia].
      unfold INV. refine (conj CTX (conj FB (conj (ex_intro _ bs0 (conj DST LBS)) (conj FR (conj ST (conj MI (conj MU WM))))))).
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition dblock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 eofv : Z) (num ln : word) (ed bs0 : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 T -> a2 = Z_to_bv 64 (C + 4) -> a3 = Z_to_bv 64 n0 -> a4 = Z_to_bv 64 eofv ->
    ro_cells usegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> length ed = 80%nat -> 0 < C -> C mod 4 = 0 ->
    rw_cells usegs m T [CB K bs0] -> 0 < T ->
    0 <= n0 <= 80 -> 3 * (n0 / 4) <= Z.of_nat K -> -1 <= eofv <= 2 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 48 ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) ->
    (T + Z.of_nat K <= lo \/ bv_unsigned sp <= T) ->
    mem_inv usegs m ->
    evt usegs (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1920c0) fc None m (seg_rom usegs)).

Theorem dblock_proof : dblock_stmt.
Proof.
  unfold dblock_stmt. intros until lo. intros -> -> -> -> -> CTX LED HC CAL DST HK HN HKN HE ST LO1 LO2 S1 S2 S3 MI.
  pose proof (ro_cells_bound _ _ _ _ CTX) as CB. unfold ectx_cells in CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply (dblock_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C T K n0 num ln ed lo); try eassumption; lia.
Qed.
