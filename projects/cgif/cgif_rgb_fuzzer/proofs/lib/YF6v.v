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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF6q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition PAREGS {imgk : img} : list (bv 5 * sv) :=
[(1%bv, SLit (0x32388 + D_150)); (2%bv, SOff 2 (-2208)); (3%bv, SOff 3 0); (4%bv, SLit TFX_TP); (8%bv, SOff 2 (-2136)); (9%bv, SOff 10 0); (10%bv, SLit TFX_INST); (11%bv, SOff 11 0);
(12%bv, SLit 8); (13%bv, SOff 2 (-2136)); (14%bv, SLit 1); (15%bv, SLit 1); (16%bv, SOff 2 (-2136)); (18%bv, SLit TFX_INST); (19%bv, SOff 11 0); (20%bv, SLit 1);
(21%bv, SOff 2 (-2136)); (22%bv, SOff 2 (-89)); (23%bv, SOff 23 0); (24%bv, SOff 24 0); (25%bv, SOff 25 0); (26%bv, SOff 26 0); (27%bv, SOff 27 0)].
Definition PAFRAMES {imgk : img} : list (Z * sv) :=
[(-2136, SOff 2 (-2120));
(-2208, SLit 1); (-2200, SLit (0x53640 + D_2c4)); (-2192, SOff 10 0); (-2184, SOff 11 0); (-2176, SOff 2 0); (-2168, SLit (0x32340 + D_150)); (-2152, SLit (0x536b0 + D_2c4));
(-64, SOff 22 0); (-56, SOff 21 0); (-48, SOff 20 0); (-40, SOff 19 0); (-32, SOff 18 0); (-24, SOff 9 0); (-16, SOff 8 0); (-8, SOff 1 0)].
Definition PACHK {imgk : img} (ss : sstate) : bool :=
regs_chk 32 ss PAREGS && frames_chk 32 ss PAFRAMES &&
match frame_chunk (ss_mem ss) (fst MIDLEN) with Some e => sv_eqb e (snd MIDLEN) | None => false end.
Definition PAST_top {imgk : img} (regs0 : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m : word -> option byte) : Prop :=
val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 len /\
Forall (fun p : bv 5 * sv => getr regs' (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGS /\
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMES.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition pa_leaf {imgk : img} (B : asyms) (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (tr : list Z)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
snd r = set_internal_inited true (set_nev (st_nev S + 1) S) /\ W' = W /\
exists regs' mem' md',
c' = cfg_at tfxsegs (0x323b8 + D_150) regs' mem' md' /\
(AR tfxsegs B ly (snd r) W' mem' md' /\ wle W W' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly (snd r) a -> ~ ascratch B ASTACK regs a ->
aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W') mem' a)) /\
PAST_top regs (Z.of_nat (length tr)) (w_H W') regs' mem' /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W') mem') (spZ regs - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
(forall a, spZ regs <= a < ly_top ly -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a) /\
qtight (snd r).
End b.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma pachk_ok {imgk : img} : forall (k : nat) (extra : list word) (regs0 : bvmap 5 word) (E0 E' : env) (H : word -> bool) ss ms,
(37 <= k)%nat -> st_ok tfxsegs E' ss (restrict H ms) -> E0 = Ereg regs0 extra -> (forall n, (n < k)%nat -> ew E' n = ew E0 n) -> ed E' = ed E0 -> PACHK ss = true ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 (bv_unsigned (ew E0 36)) /\
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGS /\
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMES.
Proof.
intros k extra regs0 E0 E' H ss ms Hk HS -> HA HD HM. unfold PACHK in HM. apply andb_prop in HM as [HM HMl]. apply andb_prop in HM as [HMr HMf].
assert (HE0 : env_agree 32 (Ereg regs0 []) E').
{ split; [|img_try (rewrite HD; img_refl)].
intros n Hn. rewrite (HA n ltac:(img_lia)). unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [img_refl | img_try (apply Nat.ltb_ge in E; img_lia)]. }
split; [|img_try (split)].
- destruct (frame_chunk (ss_mem ss) (fst MIDLEN)) as [e|] eqn:Fc; [|img_try (discriminate HMl)]. apply sv_eqb_eq in HMl. (subst e; cbv beta).
pose proof (frame_chunk_val H E' ss ms (fst MIDLEN) (snd MIDLEN) HS Fc) as V.
rewrite (HA 2%nat ltac:(img_lia)) in V. unfold MIDLEN in V |- *. cbn [fst snd sv_denot] in V |- *.
rewrite (HA 36%nat ltac:(img_lia)), Z.add_0_r, Z_to_bv_bv_unsigned in V. img_exact V.
- img_exact (regs_chk_ok 32 (Ereg regs0 []) E' H ss ms PAREGS HS HE0 HMr).
- img_exact (frames_chk_ok 32 (Ereg regs0 []) E' H ss ms PAFRAMES HS HE0 ltac:(img_lia) HMf).
Qed.
End c.
