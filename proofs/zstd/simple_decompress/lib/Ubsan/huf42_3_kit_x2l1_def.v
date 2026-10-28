(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_x2_defs.
Import ListNotations.
Open Scope Z_scope.

Lemma x2d_fw_hi16 : forall X v, X / 65536 = v -> (Z.shiftr X 16) mod 2^16 = v mod 2^16.
Proof.
  intros X v H. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536. rewrite H. reflexivity.
Qed.

Lemma x2d_fw_al : forall D q, D mod 2 = 0 -> Z.land (D + 4 + 4 * q) 1 = 0.
Proof.
  intros D q H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
  Z.div_mod_to_equations. lia.
Qed.
Lemma x2d_fw_lor16 : forall a b, 0 <= a < 65536 -> 0 <= b < 65536 -> 0 <= Z.lor a b < 65536.
Proof.
  intros a b Ha Hb. assert (N : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact N|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
  change 65536 with (2^16). apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 16 ltac:(lia))).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|NA]; [cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 a 16 ltac:(lia))). change (2^16) with 65536. lia.
  - destruct (Z.eq_dec b 0) as [->|NB]; [cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 b 16 ltac:(lia))). change (2^16) with 65536. lia.
Qed.

Lemma x2d_fw_lo2 : forall sv bs M, 0 <= sv < 256 -> 0 <= bs < 65536 -> M = 2^64 -> 0 <= Z.lor ((Z.shiftl sv 8) mod M) bs < 65536.
Proof.
  intros sv bs M Hs Hb EM. subst M. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_small by (change (2^64) with 18446744073709551616; lia). apply x2d_fw_lor16; lia.
Qed.

Lemma x2d_fw_lo2n : forall sv bs, 0 <= sv < 256 -> 0 <= bs < 65536 -> 0 <= Z.lor (Z.shiftl sv 8) bs < 65536.
Proof.
  intros sv bs Hs Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. apply x2d_fw_lor16; lia.
Qed.

Lemma x2d_fw_or_r : forall lo v, 0 <= lo < 65536 -> 0 <= v < 65536 ->
  0 <= Z.lor (v * 65536) lo < 4294967296 /\ Z.lor (v * 65536) lo / 65536 = v.
Proof.
  intros lo v Hl Hv. replace (v * 65536) with (v * 2^16) by reflexivity.
  rewrite lor_disj_add by ((try change (2^16) with 65536); lia).
  change (2^16) with 65536. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma x2d_fw_or_l : forall lo v, 0 <= lo < 65536 -> 0 <= v < 65536 ->
  0 <= Z.lor lo (v * 65536) < 4294967296 /\ Z.lor lo (v * 65536) / 65536 = v.
Proof. intros lo v Hl Hv. rewrite Z.lor_comm. apply x2d_fw_or_r; assumption. Qed.

Lemma x2d_fw_rep_core : forall X v, 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= X * 4294967296 + X < 2^64
  /\ (Z.shiftr (X * 4294967296 + X) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (X * 4294967296 + X) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X v XR XV VR. subst v. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616. change (2^16) with 65536. change (2^48) with 281474976710656.
  split; [lia|]. split; Z.div_mod_to_equations; lia.
Qed.

Lemma x2d_fw_e1 : forall X, 0 <= X < 4294967296 -> Z.lor ((Z.shiftl X 32) mod 2^64) X = X * 4294967296 + X.
Proof.
  intros X XR. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (X * 2^32)) by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; lia).
  rewrite lor_disj_add by ((try change (2^32) with 4294967296); lia). reflexivity.
Qed.

Lemma x2d_fw_rep : forall X M v, M = 2^64 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) X < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) X) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) X) 48) mod 2^16 = v mod 2^16.
Proof. intros X M v EM XR XV VR. subst M. rewrite (x2d_fw_e1 X XR). apply x2d_fw_rep_core; assumption. Qed.

Lemma x2d_fw_rep_m : forall X M K v, M = 2^64 -> K = 2^32 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) (X mod K) < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (X mod K)) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (X mod K)) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X M K v EM EK XR XV VR. subst K. rewrite (Z.mod_small X (2^32)) by (change (2^32) with 4294967296; lia).
  apply x2d_fw_rep; assumption.
Qed.

Lemma x2d_fw_rep_s : forall X M M' v, M = 2^64 -> M' = 2^64 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32) < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32)) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32)) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X M M' v EM EM' XR XV VR. subst M'.
  replace (Z.shiftr ((Z.shiftl X 32) mod 2^64) 32) with X.
  - apply x2d_fw_rep; assumption.
  - rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; lia).
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul; [reflexivity | lia].
Qed.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Ltac x2d_chk :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "UK" in
      first [ if_cases K; zify_cond K; [exfalso; lia | clear K]
            | if_cases K; zify_cond K; [clear K | exfalso; lia] ]
  | |- _ => idtac
  end.

#[local] Ltac x2d_lo := first [ lia | apply x2d_fw_lo2; first [ reflexivity | lia ] | apply x2d_fw_lo2n; lia ].

Section L1.
  Variables (ra gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP DT SYM : Z) (m0 : fmem) (cw0 : list Z)
            (syb : list byte) (pos bg en nb bs : Z) (Q : machine_state -> Prop) (lv : Z).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTE : DT mod 2 = 0.
  Hypothesis SYL : 4096 <= SYM.  Hypothesis SYH : SYM + zlen syb < 2^47.
  Hypothesis SEP : DT + HUF_DTABLE_BYTES <= SYM \/ SYM + zlen syb <= DT.
  Hypothesis BGR : 0 <= bg <= en.  Hypothesis ENR : en <= zlen syb.  Hypothesis POSR : 0 <= pos.
  Hypothesis NBR : 0 <= nb <= 12.  Hypothesis BSR : 0 <= bs < 2^16.  Hypothesis LVR : lv = 1 \/ lv = 2.

  Notation ST pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition KE1 (n : Z) : Prop :=
    forall m' cw' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
      mem_inv usegs m' -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m' -> wmono usegs m0 m' ->
      x2_cells m' DT cw' -> cells_written cw0 cw' pos n (nb + 256 * lv) ->
      evt usegs Q (ST 0x259ec m' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).

  Lemma x2d_in : forall (j : nat) r m cw (C R q E S0 D D2 D3 D4 : Z) (x7 x11 x12 x13 x15 x16 x28 x29 x30 : word),
    Z.to_nat (R - r) = j -> 0 <= r < R -> 0 <= C -> pos + C + 8 * R <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (C + 8 * r) (nb + 256 * lv) ->
    q = DT + 4 + 4 * (pos + C + 8 * r) -> E = DT + 4 + 4 * (pos + C + 8 * R) -> S0 = 0 ->
    D4 mod 2^16 = (nb + 256 * lv) mod 2^16 -> D2 mod 2^16 = (nb + 256 * lv) mod 2^16 ->
    (forall m' cw' (q' : Z), mem_inv usegs m' -> munch [(DT + 4, DT + 16388)] m0 m' -> wmono usegs m0 m' ->
       x2_cells m' DT cw' -> bytes_at usegs m' SYM syb -> cells_written cw0 cw' pos (C + 8 * R) (nb + 256 * lv) -> q' = E ->
       evt usegs Q (ST 0x25844 m' (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) x7 (Z_to_bv 64 S0) (Z_to_bv 64 D) (Z_to_bv 64 q') x11 x12 x13
                      (Z_to_bv 64 (-9)) x15 x16 (Z_to_bv 64 (-17)) (Z_to_bv 64 D2) (Z_to_bv 64 D3) (Z_to_bv 64 D4) x28 x29 x30
                      (Z_to_bv 64 E))) ->
    evt usegs Q (ST 0x257e8 m (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) x7 (Z_to_bv 64 S0) (Z_to_bv 64 D) (Z_to_bv 64 q) x11 x12 x13
                   (Z_to_bv 64 (-9)) x15 x16 (Z_to_bv 64 (-17)) (Z_to_bv 64 D2) (Z_to_bv 64 D3) (Z_to_bv 64 D4) x28 x29 x30
                   (Z_to_bv 64 E)).
  Proof using All.
    pose proof DTH as DTH'. pose proof SEP as SEP'. unfold HUF_DTABLE_BYTES in DTH', SEP'.
    induction j as [|j IH]; intros r m cw C R q E S0 D D2 D3 D4 x7 x11 x12 x13 x15 x16 x28 x29 x30
      EJ RR C0 CB MI MU WM (CW & CWL) SYB CWR -> -> -> W4 W2 K; [exfalso; lia|].
    zstep. x2d_chk.
    u16st CW (2 * (pos + C + 8 * r)) D; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 1) (nb + 256 * lv); [exact W4|].
    u16st CW (2 * (pos + C + 8 * r) + 2) D3; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 3) (nb + 256 * lv); [exact W2|].
    zstep. x2d_chk.
    u16st CW (2 * (pos + C + 8 * r) + 4) D; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 5) (nb + 256 * lv); [exact W4|].
    u16st CW (2 * (pos + C + 8 * r) + 6) D3; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 7) (nb + 256 * lv); [exact W2|].
    zstep. x2d_chk.
    u16st CW (2 * (pos + C + 8 * r) + 8) D; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 9) (nb + 256 * lv); [exact W4|].
    u16st CW (2 * (pos + C + 8 * r) + 10) D3; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 11) (nb + 256 * lv); [exact W2|].
    zstep. x2d_chk.
    u16st CW (2 * (pos + C + 8 * r) + 12) D; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 13) (nb + 256 * lv); [exact W4|].
    u16st CW (2 * (pos + C + 8 * r) + 14) D3; [reflexivity|].
    u16st CW (2 * (pos + C + 8 * r) + 15) (nb + 256 * lv); [exact W2|].
    zstep. x2d_chk.
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + (C + 8 * r)) 8 (nb + 256 * lv)) by (subst cw'; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (C + 8 * r) 8 (nb + 256 * lv) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    lazymatch type of CW with u8arr _ ?mm _ _ => assert (CWS' : x2_cells mm DT cw') by (split; assumption) end.
    zstep. if_cases KB; zify_cond KB.
    all: lazymatch type of KB with
         | ~ _ =>
             replace (C + 8 * r + 8) with (C + 8 * (r + 1)) in CWR' by lia;
             eapply (IH (r + 1) _ cw' C R); first [ eassumption | lia ]
         | _ =>
             replace (C + 8 * r + 8) with (C + 8 * R) in CWR' by lia;
             eapply K; first [ eassumption | lia ]
         end.
  Qed.

  Lemma x2_l1_def_k : forall j k m cw (L A0 A1 A2 HI T3 T4 : Z) (x8 x9 x18 x19 x20 x31 : word),
    16 <= L <= 4096 -> L mod 8 = 0 ->
    KE1 (L * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + L * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (L * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + L * k) -> A1 = SYM + bg + k -> A2 = SYM + en ->
    HI = lv * 2^24 + nb * 2^16 -> T3 = 4 * L -> T4 = 4 * L ->
    evt usegs Q (ST 0x257a4 m (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) (Z_to_bv 64 HI) x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 1) (Z_to_bv 64 (-9)) (Z_to_bv 64 bs) (Z_to_bv 64 lv) (Z_to_bv 64 (-17)) x18 x19 x20
                   (Z_to_bv 64 T3) (Z_to_bv 64 T4) (Z_to_bv 64 (-1)) x31).
  Proof using All.
    pose proof DTH as DTH'. pose proof SEP as SEP'. unfold HUF_DTABLE_BYTES in DTH', SEP'.
    induction j as [|j IH]; intros k m cw L A0 A1 A2 HI T3 T4 x8 x9 x18 x19 x20 x31
      LR LM KE EJ KR PH MI MU WM CWS SYB CWR EA0 EA1 EA2 EHI ET3 ET4; [exfalso; lia|].
    subst A0 A1 A2 T3 T4.
    assert (EHI' : HI = (nb + 256 * lv) * 65536) by (rewrite EHI; first [ring | lia]). clear EHI. subst HI.
    assert (EXR : exists R, L = 8 * R) by (exists (L / 8); pose proof (Z.div_mod L 8 ltac:(lia)) as X; lia).
    destruct EXR as (R & ER).
    assert (CB1 : L * (k + 1) <= L * (en - bg)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (CB : 0 <= L * k /\ pos + L * k + L <= 4096) by (split; [apply Z.mul_nonneg_nonneg; lia | lia]).
    assert (EXC : exists C, C = L * k) by (eexists; reflexivity). destruct EXC as (C & EC).
    rewrite <- EC in CWR, CB |- *. destruct CB as (C0 & CB).
    assert (EC1 : L * (k + 1) = C + 8 * R) by (rewrite EC; first [lia | nia]).
    clear CB1.
    unfold HUF_DTABLE_BYTES in MU.
    lbyte SYB.
    lazymatch goal with |- context [bv_unsigned (nth ?i syb ?d)] =>
      assert (SVR : 0 <= bv_unsigned (nth i syb d) < 256)
        by (pose proof (bv_unsigned_in_range 8 (nth i syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth i syb d)) as sv eqn:ESV; clear ESV end.
    zstep. if_cases KL; zify_cond KL; [| zstep; zstep].
    all: (let v := reg_val 31 in lazymatch v with Z_to_bv 64 ?e =>
            assert (TR : 0 <= e < 65536) by x2d_lo; remember e as T eqn:ET; clear ET end).
    all: zstep.
    all: zstep. all: x2d_chk.
    all: zstep. all: x2d_chk.
    all: zstep. all: x2d_chk.
    all: do 9 zstep.
    all: assert (XF : 0 <= Z.lor T ((nb + 256 * lv) * 65536) < 4294967296 /\ Z.lor T ((nb + 256 * lv) * 65536) / 65536 = nb + 256 * lv)
           by (apply x2d_fw_or_l; lia).
    all: destruct XF as (XR & XV).
    all: (let v := reg_val 9 in lazymatch v with Z_to_bv 64 ?d =>
            assert (DW : 0 <= d < 2^64 /\ (Z.shiftr d 16) mod 2^16 = (nb + 256 * lv) mod 2^16
                         /\ (Z.shiftr d 48) mod 2^16 = (nb + 256 * lv) mod 2^16)
              by (first [ apply x2d_fw_rep_s | apply x2d_fw_rep | apply x2d_fw_rep_m ];
                  first [ reflexivity | exact XR | exact XV | lia ]) end).
    all: destruct DW as (DR & D16 & D48).
    all: eapply (x2d_in (Z.to_nat (R - 0)) 0 _ cw C R).
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- cells_written _ _ _ _ _ => rewrite Z.mul_0_r, Z.add_0_r; exact CWR
         | |- Z.land _ 1 = 0 =>
             first [ apply x2d_fw_al; exact DTE
                   | change 1 with (Z.ones 1); rewrite Z.land_ones by lia; change (2^1) with 2; Z.div_mod_to_equations; lia ]
         | |- _ => first [ eassumption | lia ]
         end.
    all: intros m' cw' q' MI' MU' WM' CWS' SYB' CWR' EQ'.
    all: zstep. all: x2d_chk.
    all: zstep.
    all: zstep. all: if_cases KB. all: zify_cond KB.
    all: lazymatch type of KB with
         | ~ _ =>
             rewrite <- EC1 in CWR';
             eapply (IH (k + 1) _ cw' L); first [ eassumption | lia | ring ]
         | _ =>
             zstep;
             assert (EK : L * (en - bg) = C + 8 * R) by (replace (en - bg) with (k + 1) by lia; exact EC1);
             unfold KE1 in KE; eapply KE;
             lazymatch goal with
             | |- cells_written _ _ _ _ _ => rewrite EK; exact CWR'
             | |- _ => eassumption
             end
         end.
  Qed.

End L1.
