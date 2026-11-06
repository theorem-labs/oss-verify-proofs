(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SSRL.

Definition srl_split (kn : list kentry) (a : expr) (s : Z) : option expr :=
  let l := lin_of a in
  let m := 2 ^ s in
  if (Z.leb 0 s && Z.ltb s 64)%bool then
  if lin_nowrap kn a then
    match lsplit_divc m (snd l) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        if lin_nowrap_l kn (fst l) rts
        then Some (EAlu ALU_ADD (unlin (0, ldiv_terms m dts)) (EAlu ALU_SRL (unlin (fst l, rts)) (ELit s)))
        else None
    (* [comment removed for export] *)
    | ((_ :: _) as dts, []) => if Z.leb 0 (fst l) then Some (mkAlu ALU_ADD (unlin (0, ldiv_terms m dts)) (ELit (fst l / m))) else None
    | _ => None
    end
  else None
  else None.

Section Sound.
Variable segs : list Segment.

Lemma lsplit_sum : forall E m ts d r, lsplit_divc m ts = (d, r) -> coeffs_div m d = true /\ tden E ts = (tden E d + tden E r)%Z.
Proof.
  intros E m ts. induction ts as [|[k a0] rest IH]; intros d r H.
  - cbn in H. injection H as <- <-. split; [reflexivity | cbn; lia].
  - cbn [lsplit_divc] in H. destruct (lsplit_divc m rest) as [d0 r0] eqn:Hs0.
    destruct (IH d0 r0 eq_refl) as [Hd Hsum].
    destruct (Z.eqb (k mod m) 0) eqn:Hk; injection H as <- <-.
    + split; [cbn [coeffs_div]; rewrite Hk, Hd; reflexivity|]. cbn [tden]. rewrite Hsum. lia.
    + split; [exact Hd|]. cbn [tden]. rewrite Hsum. lia.
Qed.

Theorem srl_split_sound : forall E M kn a s e', know_ok segs E M kn -> srl_split kn a s = Some e' ->
  edenot E e' = alu64 ALU_SRL (edenot E a) (Z_to_bv 64 s).
Proof.
  intros E M kn a s e' HK H. unfold srl_split in H.
  destruct (Z.leb 0 s && Z.ltb s 64)%bool eqn:Hs; [|discriminate]. apply andb_prop in Hs as [Hs0 Hs1].
  apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs1.
  destruct (lin_nowrap kn a) eqn:Hnw; [|discriminate].
  destruct (lsplit_divc (2 ^ s) (snd (lin_of a))) as [dts rts] eqn:Hsp.
  destruct dts as [|d1 dts']; [discriminate|]. destruct rts as [|r1 rts'].
  { (* [comment removed for export] *)
    destruct (Z.leb 0 (fst (lin_of a))) eqn:Hc0; [|discriminate]. apply Z.leb_le in Hc0. injection H as <-.
    assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    destruct (lsplit_sum E _ _ _ _ Hsp) as [Hdiv Hsum].
    pose proof (lin_nowrap_sound segs E M kn a HK Hnw) as Hval. rewrite Hsum in Hval.
    replace (tden E []) with 0%Z in Hval by reflexivity.
    set (c := fst (lin_of a)) in *.
    rewrite (ldiv_terms_sound E (2 ^ s) (d1 :: dts') Hp Hdiv) in Hval.
    set (A := tden E (ldiv_terms (2 ^ s) (d1 :: dts'))) in *.
    pose proof (unlin_sound E (0, ldiv_terms (2 ^ s) (d1 :: dts'))) as [q Hq]. unfold lden, uE in Hq. cbn [fst snd] in Hq. fold A in Hq.
    change (let (k, a0) := d1 in (k / 2 ^ s, a0) :: ldiv_terms (2 ^ s) dts') with (ldiv_terms (2 ^ s) (d1 :: dts')).
    set (U := unlin (0, ldiv_terms (2 ^ s) (d1 :: dts'))) in *. clearbody U.
    rewrite mkAlu_denot. cbn [edenot]. rewrite alu_srl. unfold v_srl.
    rewrite (u_lit64a s), (Z.mod_small s (2 ^ 64)) by lia. rewrite (Z.mod_small s 64) by lia.
    rewrite Hval. rewrite !Z.shiftr_div_pow2 by lia.
    replace (c + (2 ^ s * A + 0)) with (A * 2 ^ s + c) by lia. rewrite Z.div_add_l by lia.
    unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite Hq. rewrite ?Z.add_mod_idemp_r by lia.
    replace (0 + A + q * 2 ^ 64 + c / 2 ^ s) with ((A + c / 2 ^ s) + q * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  destruct (lin_nowrap_l kn (fst (lin_of a)) (r1 :: rts')) eqn:Hnr; [|discriminate]. injection H as <-.
  assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  destruct (lsplit_sum E _ _ _ _ Hsp) as [Hdiv Hsum].
  pose proof (lin_nowrap_sound segs E M kn a HK Hnw) as Hval. rewrite Hsum in Hval.
  set (c := fst (lin_of a)) in *.
  unfold lin_nowrap_l in Hnr.
  destruct (lin_range (erange kn) c (r1 :: rts')) as [[lo2 hi2]|] eqn:Hlr; [|discriminate].
  apply andb_prop in Hnr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (lin_range_sound E (erange kn) (fun a0 lo0 hi0 Ha => erange_sound segs E M kn a0 lo0 hi0 HK Ha) _ _ _ _ Hlr) as HR.
  set (T := tden E (r1 :: rts')) in *.
  assert (HuR : bv_unsigned (edenot E (unlin (c, r1 :: rts'))) = c + T).
  { pose proof (unlin_sound E (c, r1 :: rts')) as [q Hq']. unfold lden, uE in Hq'. cbn [fst snd] in Hq'.
    pose proof (u64_range (edenot E (unlin (c, r1 :: rts')))). fold T in Hq'. nia. }
  rewrite (ldiv_terms_sound E (2 ^ s) (d1 :: dts') Hp Hdiv) in Hval.
  set (A := tden E (ldiv_terms (2 ^ s) (d1 :: dts'))) in *.
  (* [comment removed for export] *)
  pose proof (unlin_sound E (0, ldiv_terms (2 ^ s) (d1 :: dts'))) as [q Hq]. unfold lden, uE in Hq. cbn [fst snd] in Hq. fold A in Hq.
  change (let (k, a0) := d1 in (k / 2 ^ s, a0) :: ldiv_terms (2 ^ s) dts') with (ldiv_terms (2 ^ s) (d1 :: dts')).
  set (U := unlin (0, ldiv_terms (2 ^ s) (d1 :: dts'))) in *. clearbody U.
  cbn [edenot]. rewrite !alu_srl. unfold v_srl. rewrite HuR.
  rewrite (u_lit64a s), (Z.mod_small s (2 ^ 64)) by lia. rewrite (Z.mod_small s 64) by lia.
  rewrite Hval. rewrite !Z.shiftr_div_pow2 by lia.
  replace (c + (2 ^ s * A + T)) with (A * 2 ^ s + (c + T)) by lia. rewrite Z.div_add_l by lia.
  unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Hq. rewrite Z.add_mod_idemp_r by lia.
  replace (0 + A + q * 2 ^ 64 + (c + T) / 2 ^ s) with ((A + (c + T) / 2 ^ s) + q * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint srl_norm (kn : list kentry) (e : expr) : expr :=
  match e with
  | EAlu o a b =>
      let a' := srl_norm kn a in let b' := srl_norm kn b in
      match o, b' with
      | ALU_SRL, ELit s => match srl_split kn a' s with Some e' => e' | None => EAlu o a' b' end
      | _, _ => EAlu o a' b'
      end
  | _ => e
  end.

Lemma srl_norm_ok : forall E M kn e, know_ok segs E M kn -> edenot E (srl_norm kn e) = edenot E e.
Proof.
  intros E M kn e HK. induction e as [z|n|o a IHa b IHb|o a _ b _|o a _ b _|o a _ b _|sx lo n a _|sx k i n]; try reflexivity.
  cbn [srl_norm].
  assert (Hg : edenot E (EAlu o (srl_norm kn a) (srl_norm kn b)) = edenot E (EAlu o a b)).
  { cbn [edenot]. rewrite IHa, IHb. reflexivity. }
  destruct o; try exact Hg.
  destruct (srl_norm kn b) as [s| | | | | | |] eqn:Hb; try exact Hg.
  destruct (srl_split kn (srl_norm kn a) s) as [e'|] eqn:Hs; [|exact Hg].
  rewrite (srl_split_sound E M kn _ _ _ HK Hs). cbn [edenot] in IHb |- *. rewrite IHa, IHb. reflexivity.
Qed.

End Sound.
End SSRL.
