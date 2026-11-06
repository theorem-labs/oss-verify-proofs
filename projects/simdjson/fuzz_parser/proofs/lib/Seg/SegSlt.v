(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegSR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S.

Module SSLT.

(* [comment removed for export] *)
Definition neg_iv (r : option (Z * Z)) : option (Z * Z) :=
  match r with Some (l, h) => if Z.ltb (- 2 ^ 63) l then Some (- h, - l) else None | None => None end.
Definition iv_meet2 (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  | Some r, None => Some r
  | None, r => r
  end.
Definition srange_pm (kn : list kentry) (e : expr) : option (Z * Z) :=
  iv_meet2 (SSR.srange kn e) (neg_iv (SSR.srange kn (mkAlu ALU_SUB (ELit 0) e))).

Definition slt_dec (kn : list kentry) (a b : expr) : option bool :=
  match srange_pm kn a with
  | None => None
  | Some (la, ha) =>
    match srange_pm kn b with
    | None => None
    | Some (lb, hb) =>
      if Z.ltb ha lb then Some true else
      if Z.leb hb la then Some false else
      if Z.leb (- 2 ^ 63) (la - hb) then
        if Z.ltb (ha - lb) (2 ^ 63) then
          match srange_pm kn (mkAlu ALU_SUB a b) with
          | Some (ld, hd) => if Z.leb 0 ld then Some false else if Z.ltb hd 0 then Some true else None
          | None => None
          end
        else None
      else None
    end
  end.

Lemma srange_pm_sound : forall segs E M kn e lo hi, know_ok segs E M kn -> srange_pm kn e = Some (lo, hi) ->
  lo <= bv_signed (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi HK H. unfold srange_pm, iv_meet2 in H.
  assert (N : forall l h, neg_iv (SSR.srange kn (mkAlu ALU_SUB (ELit 0) e)) = Some (l, h) -> l <= bv_signed (edenot E e) <= h).
  { intros l h Hn. unfold neg_iv in Hn.
    destruct (SSR.srange kn (mkAlu ALU_SUB (ELit 0) e)) as [[l0 h0]|] eqn:Hs; [|discriminate].
    destruct (Z.ltb (- 2 ^ 63) l0) eqn:C; [|discriminate]. injection Hn as <- <-. apply Z.ltb_lt in C.
    pose proof (SSR.srange_sound segs E M kn _ l0 h0 HK Hs) as S.
    assert (D : bv_signed (edenot E (mkAlu ALU_SUB (ELit 0) e)) = - bv_signed (edenot E e)).
    { rewrite mkAlu_denot, alu_sub. unfold v_sub. apply SSR.s_of_eqm.
      - rewrite Z_to_bv_unsigned, edenot_lit, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
        destruct (SSR.s_eqm (edenot E e)) as [q Hq].
        pose proof (Z.div_mod (0 mod 2 ^ 64 - bv_unsigned (edenot E e)) (2 ^ 64) ltac:(lia)) as DM.
        exists (q - (0 mod 2 ^ 64 - bv_unsigned (edenot E e)) / 2 ^ 64). rewrite Z.mod_0_l in * by lia. lia.
      - pose proof (SSR.s_range (edenot E e)) as R.
        assert (bv_signed (edenot E e) <> - 2 ^ 63).
        { intros Heq. (* [comment removed for export] *)
          assert (X : bv_signed (edenot E (mkAlu ALU_SUB (ELit 0) e)) = - 2 ^ 63).
          { rewrite mkAlu_denot, alu_sub. unfold v_sub. apply SSR.s_of_eqm; [|lia].
            rewrite Z_to_bv_unsigned, edenot_lit, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
            destruct (SSR.s_eqm (edenot E e)) as [q Hq].
            pose proof (Z.div_mod (0 mod 2 ^ 64 - bv_unsigned (edenot E e)) (2 ^ 64) ltac:(lia)) as DM.
            exists (q - (0 mod 2 ^ 64 - bv_unsigned (edenot E e)) / 2 ^ 64 + 1). rewrite Z.mod_0_l in * by lia. lia. }
          lia. }
        lia. }
    lia. }
  destruct (SSR.srange kn e) as [[l1 h1]|] eqn:Hs1.
  - pose proof (SSR.srange_sound segs E M kn e l1 h1 HK Hs1) as S1.
    destruct (neg_iv (SSR.srange kn (mkAlu ALU_SUB (ELit 0) e))) as [[l2 h2]|] eqn:Hn.
    + injection H as <- <-. pose proof (N l2 h2 eq_refl). lia.
    + injection H as <- <-. exact S1.
  - exact (N lo hi H).
Qed.

Lemma slt_dec_sound : forall segs E M kn a b r, know_ok segs E M kn -> slt_dec kn a b = Some r ->
  Z.ltb (bv_signed (edenot E a)) (bv_signed (edenot E b)) = r.
Proof.
  intros segs E M kn a b r HK H. unfold slt_dec in H.
  destruct (srange_pm kn a) as [[la ha]|] eqn:Ra; [|discriminate].
  destruct (srange_pm kn b) as [[lb hb]|] eqn:Rb; [|discriminate].
  pose proof (srange_pm_sound segs E M kn a la ha HK Ra) as Sa.
  pose proof (srange_pm_sound segs E M kn b lb hb HK Rb) as Sb.
  destruct (Z.ltb ha lb) eqn:C1.
  { injection H as <-. apply Z.ltb_lt in C1. apply Z.ltb_lt. lia. }
  destruct (Z.leb hb la) eqn:C2.
  { injection H as <-. apply Z.leb_le in C2. apply Z.ltb_ge. lia. }
  destruct (Z.leb (- 2 ^ 63) (la - hb)) eqn:C3; [|discriminate].
  destruct (Z.ltb (ha - lb) (2 ^ 63)) eqn:C4; [|discriminate].
  apply Z.leb_le in C3. apply Z.ltb_lt in C4.
  destruct (srange_pm kn (mkAlu ALU_SUB a b)) as [[ld hd]|] eqn:Rd; [|discriminate].
  pose proof (srange_pm_sound segs E M kn _ ld hd HK Rd) as Sd.
  assert (D : bv_signed (edenot E (mkAlu ALU_SUB a b)) = bv_signed (edenot E a) - bv_signed (edenot E b)).
  { rewrite mkAlu_denot, alu_sub. unfold v_sub. apply SSR.s_of_eqm; [|lia].
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    destruct (SSR.s_eqm (edenot E a)) as [qa Ha]. destruct (SSR.s_eqm (edenot E b)) as [qb Hb].
    pose proof (Z.div_mod (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) (2 ^ 64) ltac:(lia)) as DM.
    exists (- ((bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) / 2 ^ 64) + qb - qa). lia. }
  rewrite D in Sd.
  destruct (Z.leb 0 ld) eqn:C5.
  { injection H as <-. apply Z.leb_le in C5. apply Z.ltb_ge. lia. }
  destruct (Z.ltb hd 0) eqn:C6; [|discriminate].
  injection H as <-. apply Z.ltb_lt in C6. apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma slt_value : forall segs E M kn a b r, know_ok segs E M kn -> slt_dec kn a b = Some r ->
  edenot E (EAlu ALU_SLT a b) = edenot E (ELit (if r then 1 else 0)).
Proof.
  intros segs E M kn a b r HK H. pose proof (slt_dec_sound segs E M kn a b r HK H) as S.
  cbn [edenot]. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite S. destruct r; reflexivity.
Qed.

End SSLT.
