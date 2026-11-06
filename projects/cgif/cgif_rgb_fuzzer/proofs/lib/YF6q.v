(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition frame_chunk (rs : smem) (off : Z) : option sv :=
match find (fun r => match YQ0b.r_base r with Some 2%nat => (YQ0b.r_lo r <=? off) && (off <? YQ0b.r_hi r) | _ => false end) rs with
| Some r => match find (fun c => YQ0b.c_off c =? off) (YQ0b.r_chunks r) with
| Some c => match YQ0b.c_val c with CVal 8%N e => Some e | _ => None end
| None => None
end
| None => None
end.
Definition regs_chk (k : nat) (ss : sstate) (L : list (bv 5 * sv)) : bool :=
forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt k (snd p)) L.
Definition frames_chk (k : nat) (ss : sstate) (L : list (Z * sv)) : bool :=
forallb (fun p => match frame_chunk (ss_mem ss) (fst p) with Some e => sv_eqb e (snd p) && sv_atoms_lt k (snd p) | None => false end) L.
Definition MIDFRAMES {imgk : img} : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0); (-40, SOff 19 0); (-48, SOff 20 0); (-56, SOff 21 0); (-64, SOff 22 0);
(-2136, SOff 2 (-2120));
(-2152, SLit (0x536b0 + D_2c4)); (-2168, SLit (0x32340 + D_150)); (-2176, SOff 2 0); (-2184, SOff 10 0); (-2192, SOff 11 0); (-2200, SLit (0x53640 + D_2c4)); (-2208, SLit 1)].
Definition MIDREGS {imgk : img} : list (bv 5 * sv) := [(2%bv, SOff 2 (-2208)); (8%bv, SOff 2 (-2136)); (9%bv, SOff 11 0); (18%bv, SLit TFX_INST); (19%bv, SOff 10 0)].
Definition MIDLEN : Z * sv := (-2128, SOff 36 0).
Definition MIDCHK {imgk : img} (ss : sstate) : bool :=
regs_chk 32 ss MIDREGS && frames_chk 32 ss MIDFRAMES &&
match frame_chunk (ss_mem ss) (fst MIDLEN) with Some e => sv_eqb e (snd MIDLEN) | None => false end.
Definition MIDST_top {imgk : img} (regs0 : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m : word -> option byte) : Prop :=
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 len /\
Forall (fun p : bv 5 * sv => getr regs' (fst p) = sv_denot (Ereg regs0 []) (snd p)) MIDREGS /\
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) MIDFRAMES.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma frame_chunk_val {imgk : img} : forall (H : word -> bool) E ss ms off e,
st_ok tfxsegs E ss (restrict H ms) -> frame_chunk (ss_mem ss) off = Some e ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) 8 (bv_unsigned (sv_denot E e)).
Proof.
intros H E ss ms off e HS HF. unfold frame_chunk in HF.
destruct (find _ (ss_mem ss)) as [r|] eqn:Fr; [|img_try (discriminate HF)].
destruct (find _ (YQ0b.r_chunks r)) as [c|] eqn:Fc; [|img_try (discriminate HF)].
apply find_some in Fr as [Inr Pr]. apply find_some in Fc as [Inc Pc].
destruct c as [coff cv]. cbn [YQ0b.c_off YQ0b.c_val] in *. destruct cv as [w v| | |]; try discriminate HF.
destruct w as [|w]; try discriminate HF. do 3 (destruct w as [w|w|]; try discriminate HF). destruct w; try discriminate HF. injection HF as ->.
apply Z.eqb_eq in Pc. (subst coff; cbv beta).
destruct (YQ0b.r_base r) as [b|] eqn:Eb; [|img_try (discriminate Pr)]. destruct b as [|[|[|b]]]; try discriminate Pr.
apply In_nth_error in Inr as [i Hi]. apply In_nth_error in Inc as [j Hj].
pose proof (st_ok_chunk_val H E ss ms i r j off 8%N e (bv_unsigned (sv_denot E e)) HS Hi Hj) as V.
rewrite Eb in V. cbn [base_val] in V. img_apply V.
- symmetry. img_apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as R. img_change (bv_modulus 64) with (2 ^ 64) in R. img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). img_exact R.
- (img_case; cbv). discriminate.
Qed.
Lemma regs_chk_ok {imgk : img} : forall (k : nat) (E0 E' : env) (H : word -> bool) ss ms (L : list (bv 5 * sv)),
st_ok tfxsegs E' ss (restrict H ms) -> env_agree k E0 E' -> regs_chk k ss L = true ->
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot E0 (snd p)) L.
Proof.
intros k E0 E' H ss ms L HS HE. unfold regs_chk. induction L as [|[r e] L IH]; intros HC; [img_try (constructor)|].
cbn [forallb] in HC. apply andb_prop in HC as [HC1 HC2]. apply andb_prop in HC1 as [Hq Ha]. cbn [fst snd] in Hq, Ha.
constructor; [|img_try (img_exact (IH HC2))]. cbn [fst snd].
rewrite (st_ok_reg_denot H E' ss ms r HS), (sv_eqb_eq _ _ Hq). img_exact (sv_denot_agree k E0 E' e HE Ha).
Qed.
Lemma frames_chk_ok {imgk : img} : forall (k : nat) (E0 E' : env) (H : word -> bool) ss ms (L : list (Z * sv)),
st_ok tfxsegs E' ss (restrict H ms) -> env_agree k E0 E' -> (2 < k)%nat -> frames_chk k ss L = true ->
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E0 2) + fst p) 8 (bv_unsigned (sv_denot E0 (snd p)))) L.
Proof.
intros k E0 E' H ss ms L HS HE Hk. unfold frames_chk. induction L as [|[off e] L IH]; intros HC; [img_try (constructor)|].
cbn [forallb] in HC. apply andb_prop in HC as [HC1 HC2]. cbn [fst snd] in HC1.
destruct (frame_chunk (ss_mem ss) off) as [e'|] eqn:Fc; [|img_try (discriminate HC1)]. apply andb_prop in HC1 as [Hq Ha].
apply sv_eqb_eq in Hq. (subst e'; cbv beta).
constructor; [|img_try (img_exact (IH HC2))]. cbn [fst snd].
rewrite <- (proj1 HE 2%nat Hk), <- (sv_denot_agree k E0 E' e HE Ha). img_exact (frame_chunk_val H E' ss ms off e HS Fc).
Qed.
Definition acall_mid {imgk : img} (B : asyms) (len : Z) (stk : Z) (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world tfxsegs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
AR tfxsegs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
MIDST_top regs len (w_H W') regs' mem' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
Definition mid_leaf {imgk : img} (B : asyms) (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfxsegs (0x323bc + D_150) regs' mem' md' /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W') mem') (spZ regs - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
acall_mid B (Z.of_nat (length tr)) ASTACK ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r).
Lemma midchk_ok {imgk : img} : forall (k : nat) (extra : list word) (regs0 : bvmap 5 word) (E' : env) (H : word -> bool) ss ms,
(37 <= k)%nat -> st_ok tfxsegs E' ss (restrict H ms) -> env_agree k (Ereg regs0 extra) E' -> MIDCHK ss = true ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 (bv_unsigned (ew (Ereg regs0 extra) 36)) /\
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot (Ereg regs0 []) (snd p)) MIDREGS /\
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) MIDFRAMES.
Proof.
intros k extra regs0 E' H ss ms Hk HS HE HM. unfold MIDCHK in HM. apply andb_prop in HM as [HM HMl]. apply andb_prop in HM as [HMr HMf].
assert (HE0 : env_agree 32 (Ereg regs0 []) E').
{ destruct HE as [HA HD]. split; [|img_try (rewrite HD; img_refl)].
intros n Hn. rewrite (HA n ltac:(img_lia)). unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [img_refl | img_try (apply Nat.ltb_ge in E; img_lia)]. }
split; [|img_try (split)].
- destruct (frame_chunk (ss_mem ss) (fst MIDLEN)) as [e|] eqn:Fc; [|img_try (discriminate HMl)]. apply sv_eqb_eq in HMl. (subst e; cbv beta).
pose proof (frame_chunk_val H E' ss ms (fst MIDLEN) (snd MIDLEN) HS Fc) as V.
rewrite (proj1 HE 2%nat ltac:(img_lia)) in V. unfold MIDLEN in V |- *. cbn [fst snd sv_denot] in V |- *.
rewrite (proj1 HE 36%nat ltac:(img_lia)), Z.add_0_r, Z_to_bv_bv_unsigned in V. img_exact V.
- img_exact (regs_chk_ok 32 (Ereg regs0 []) E' H ss ms MIDREGS HS HE0 HMr).
- img_exact (frames_chk_ok 32 (Ereg regs0 []) E' H ss ms MIDFRAMES HS HE0 ltac:(img_lia) HMf).
Qed.
End d.
