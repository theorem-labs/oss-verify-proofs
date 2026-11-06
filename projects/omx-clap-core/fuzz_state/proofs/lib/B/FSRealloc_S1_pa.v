(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_state image B, realloc segment S1 (a Theorem Labs lane, 2026-10-29).
   The register / frame checks at Allocate's entry (PAREGS, PAFRAMES, PAST_top, pachk_ok) and the prefix leaf pa_leaf.
   The B twin of lib/A/FSRealloc_S1_pa.v (a working branch ce07ca45bca; port of cgif_rgb_fuzzer
   lib/YF6q.v + YF6v.v).
   Every B address literal is the A file's at fs-addr-map.tsv's B column (internal path), each checked by
   capstone (RV64, no compressed instructions) over the pinned fuzz_state.asan-ubsan (sha256 5ac5ce0954f87e2d...):
   same instruction word at the A and the B address.
   The words: ra = 0x32a04 [0x32994] (`mv s4, a0`, the return pc of Reallocate's 0x32a00 `jal -0xa9c` to Allocate
   0x31f64); the saved return pcs 0x53690 [0x53620] (interceptor 0x5368c `jal -0x20da0`, `addi sp, sp, 0x70`) and
   0x32988 [0x32918] (asan_realloc 0x32984 `jal 0x14`, `beqz a0, -0x20`); the trace pc 0x53620 [0x535b0] (0x5361c
   `jal 0x20314`, `auipc a1, 0x4c`).  pa_leaf states fs's allocator relation FSupoison.ARU (FS_ARX's form). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: the image-B twin of lib/A/FSRealloc_S1_pa.v (a working branch ce07ca45bca): image B's modules (lib/B/Yxxx for lib/A/Axxx) and fuzz_state.asan-ubsan's addresses (a Theorem Labs lane's realloc-thin/fs-addr-map.tsv, capstone-checked). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YF0x.

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
Definition frame_chunk (rs : smem) (off : Z) : option sv :=
match find (fun r => match YP09.r_base r with Some 2%nat => (YP09.r_lo r <=? off) && (off <? YP09.r_hi r) | _ => false end) rs with
| Some r => match find (fun c => YP09.c_off c =? off) (YP09.r_chunks r) with
| Some c => match YP09.c_val c with CVal 8%N e => Some e | _ => None end
| None => None
end
| None => None
end.
Definition regs_chk (k : nat) (ss : sstate) (L : list (bv 5 * sv)) : bool :=
forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt k (snd p)) L.
Definition frames_chk (k : nat) (ss : sstate) (L : list (Z * sv)) : bool :=
forallb (fun p => match frame_chunk (ss_mem ss) (fst p) with Some e => sv_eqb e (snd p) && sv_atoms_lt k (snd p) | None => false end) L.
Definition MIDFRAMES : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0); (-40, SOff 19 0); (-48, SOff 20 0); (-56, SOff 21 0); (-64, SOff 22 0);
(-2136, SOff 2 (-2120));
(-2152, SLit 0x53690); (-2168, SLit 0x32988); (-2176, SOff 2 0); (-2184, SOff 10 0); (-2192, SOff 11 0); (-2200, SLit 0x53620); (-2208, SLit 1)].
Definition MIDREGS : list (bv 5 * sv) := [(2%bv, SOff 2 (-2208)); (8%bv, SOff 2 (-2136)); (9%bv, SOff 11 0); (18%bv, SLit TFIB_INST); (19%bv, SOff 10 0)].
Definition MIDLEN : Z * sv := (-2128, SOff 36 0).
Definition MIDCHK (ss : sstate) : bool :=
regs_chk 32 ss MIDREGS && frames_chk 32 ss MIDFRAMES &&
match frame_chunk (ss_mem ss) (fst MIDLEN) with Some e => sv_eqb e (snd MIDLEN) | None => false end.
Definition MIDST_top (regs0 : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m : word -> option byte) : Prop :=
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 len /\
Forall (fun p : bv 5 * sv => getr regs' (fst p) = sv_denot (Ereg regs0 []) (snd p)) MIDREGS /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) MIDFRAMES.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma frame_chunk_val : forall (H : word -> bool) E ss ms off e,
st_ok tfibsegs E ss (restrict H ms) -> frame_chunk (ss_mem ss) off = Some e ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) 8 (bv_unsigned (sv_denot E e)).
Proof.
intros H E ss ms off e HS HF. unfold frame_chunk in HF.
destruct (find _ (ss_mem ss)) as [r|] eqn:Fr; [|discriminate HF].
destruct (find _ (YP09.r_chunks r)) as [c|] eqn:Fc; [|discriminate HF].
apply find_some in Fr as [Inr Pr]. apply find_some in Fc as [Inc Pc].
destruct c as [coff cv]. cbn [YP09.c_off YP09.c_val] in *. destruct cv as [w v| | |]; try discriminate HF.
destruct w as [|w]; try discriminate HF. do 3 (destruct w as [w|w|]; try discriminate HF). destruct w; try discriminate HF. injection HF as ->.
apply Z.eqb_eq in Pc. subst coff.
destruct (YP09.r_base r) as [b|] eqn:Eb; [|discriminate Pr]. destruct b as [|[|[|b]]]; try discriminate Pr.
apply In_nth_error in Inr as [i Hi]. apply In_nth_error in Inc as [j Hj].
pose proof (st_ok_chunk_val H E ss ms i r j off 8%N e (bv_unsigned (sv_denot E e)) HS Hi Hj) as V.
rewrite Eb in V. cbn [base_val] in V. apply V.
- symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as R. change (bv_modulus 64) with (2 ^ 64) in R. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact R.
- cbv. discriminate.
Qed.
Lemma regs_chk_ok : forall (k : nat) (E0 E' : env) (H : word -> bool) ss ms (L : list (bv 5 * sv)),
st_ok tfibsegs E' ss (restrict H ms) -> env_agree k E0 E' -> regs_chk k ss L = true ->
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot E0 (snd p)) L.
Proof.
intros k E0 E' H ss ms L HS HE. unfold regs_chk. induction L as [|[r e] L IH]; intros HC; [constructor|].
cbn [forallb] in HC. apply andb_prop in HC as [HC1 HC2]. apply andb_prop in HC1 as [Hq Ha]. cbn [fst snd] in Hq, Ha.
constructor; [|exact (IH HC2)]. cbn [fst snd].
rewrite (st_ok_reg_denot H E' ss ms r HS), (sv_eqb_eq _ _ Hq). exact (sv_denot_agree k E0 E' e HE Ha).
Qed.
Lemma frames_chk_ok : forall (k : nat) (E0 E' : env) (H : word -> bool) ss ms (L : list (Z * sv)),
st_ok tfibsegs E' ss (restrict H ms) -> env_agree k E0 E' -> (2 < k)%nat -> frames_chk k ss L = true ->
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E0 2) + fst p) 8 (bv_unsigned (sv_denot E0 (snd p)))) L.
Proof.
intros k E0 E' H ss ms L HS HE Hk. unfold frames_chk. induction L as [|[off e] L IH]; intros HC; [constructor|].
cbn [forallb] in HC. apply andb_prop in HC as [HC1 HC2]. cbn [fst snd] in HC1.
destruct (frame_chunk (ss_mem ss) off) as [e'|] eqn:Fc; [|discriminate HC1]. apply andb_prop in HC1 as [Hq Ha].
apply sv_eqb_eq in Hq. subst e'.
constructor; [|exact (IH HC2)]. cbn [fst snd].
rewrite <- (proj1 HE 2%nat Hk), <- (sv_denot_agree k E0 E' e HE Ha). exact (frame_chunk_val H E' ss ms off e HS Fc).
Qed.
Definition acall_mid (B : asyms) (len : Z) (stk : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
AR tfibsegs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
MIDST_top regs len (w_H W') regs' mem' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
Definition mid_leaf (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs 0x32a04 regs' mem' md' /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
acall_mid B (Z.of_nat (length tr)) ASTACK ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r).
Lemma midchk_ok : forall (k : nat) (extra : list word) (regs0 : bvmap 5 word) (E' : env) (H : word -> bool) ss ms,
(37 <= k)%nat -> st_ok tfibsegs E' ss (restrict H ms) -> env_agree k (Ereg regs0 extra) E' -> MIDCHK ss = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 (bv_unsigned (ew (Ereg regs0 extra) 36)) /\
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot (Ereg regs0 []) (snd p)) MIDREGS /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) MIDFRAMES.
Proof.
intros k extra regs0 E' H ss ms Hk HS HE HM. unfold MIDCHK in HM. apply andb_prop in HM as [HM HMl]. apply andb_prop in HM as [HMr HMf].
assert (HE0 : env_agree 32 (Ereg regs0 []) E').
{ destruct HE as [HA HD]. split; [|rewrite HD; reflexivity].
intros n Hn. rewrite (HA n ltac:(lia)). unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
split; [|split].
- destruct (frame_chunk (ss_mem ss) (fst MIDLEN)) as [e|] eqn:Fc; [|discriminate HMl]. apply sv_eqb_eq in HMl. subst e.
pose proof (frame_chunk_val H E' ss ms (fst MIDLEN) (snd MIDLEN) HS Fc) as V.
rewrite (proj1 HE 2%nat ltac:(lia)) in V. unfold MIDLEN in V |- *. cbn [fst snd sv_denot] in V |- *.
rewrite (proj1 HE 36%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned in V. exact V.
- exact (regs_chk_ok 32 (Ereg regs0 []) E' H ss ms MIDREGS HS HE0 HMr).
- exact (frames_chk_ok 32 (Ereg regs0 []) E' H ss ms MIDFRAMES HS HE0 ltac:(lia) HMf).
Qed.
End d.


Definition PAREGS : list (bv 5 * sv) :=
[(1%bv, SLit 0x32a04); (2%bv, SOff 2 (-2208)); (3%bv, SOff 3 0); (4%bv, SLit TFIB_TP); (8%bv, SOff 2 (-2136)); (9%bv, SOff 10 0); (10%bv, SLit TFIB_INST); (11%bv, SOff 11 0);
(12%bv, SLit 8); (13%bv, SOff 2 (-2136)); (14%bv, SLit 1); (15%bv, SLit 1); (16%bv, SOff 2 (-2136)); (18%bv, SLit TFIB_INST); (19%bv, SOff 11 0); (20%bv, SLit 1);
(21%bv, SOff 2 (-2136)); (22%bv, SOff 2 (-89)); (23%bv, SOff 23 0); (24%bv, SOff 24 0); (25%bv, SOff 25 0); (26%bv, SOff 26 0); (27%bv, SOff 27 0)].
Definition PAFRAMES : list (Z * sv) :=
[(-2136, SOff 2 (-2120));
(-2208, SLit 1); (-2200, SLit 0x53620); (-2192, SOff 10 0); (-2184, SOff 11 0); (-2176, SOff 2 0); (-2168, SLit 0x32988); (-2152, SLit 0x53690);
(-64, SOff 22 0); (-56, SOff 21 0); (-48, SOff 20 0); (-40, SOff 19 0); (-32, SOff 18 0); (-24, SOff 9 0); (-16, SOff 8 0); (-8, SOff 1 0)].
Definition PACHK (ss : sstate) : bool :=
regs_chk 32 ss PAREGS && frames_chk 32 ss PAFRAMES &&
match frame_chunk (ss_mem ss) (fst MIDLEN) with Some e => sv_eqb e (snd MIDLEN) | None => false end.
Definition PAST_top (regs0 : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 len /\
Forall (fun p : bv 5 * sv => getr regs' (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGS /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMES.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition pa_leaf (B : asyms) (Up : list (Z * Z)) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (tr : list Z)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
snd r = set_internal_inited true (set_nev (st_nev S + 1) S) /\ W' = W /\
exists regs' mem' md',
c' = cfg_at tfibsegs 0x31f64 regs' mem' md' /\
(FSupoison.ARU tfibsegs B ly (snd r) Up W' mem' md' /\ wle W W' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly (snd r) a -> ~ ascratch B ASTACK regs a ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(* the same frame on the raw memory (c5's seg_pre states both) *)
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W') mem' a)) /\
PAST_top regs (Z.of_nat (length tr)) (w_H W') regs' mem' /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
(forall a, spZ regs <= a < ly_top ly -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
qtight (snd r).
End b.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pachk_ok : forall (k : nat) (extra : list word) (regs0 : bvmap 5 word) (E0 E' : env) (H : word -> bool) ss ms,
(37 <= k)%nat -> st_ok tfibsegs E' ss (restrict H ms) -> E0 = Ereg regs0 extra -> (forall n, (n < k)%nat -> ew E' n = ew E0 n) -> ed E' = ed E0 -> PACHK ss = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 (bv_unsigned (ew E0 36)) /\
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGS /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMES.
Proof.
intros k extra regs0 E0 E' H ss ms Hk HS -> HA HD HM. unfold PACHK in HM. apply andb_prop in HM as [HM HMl]. apply andb_prop in HM as [HMr HMf].
assert (HE0 : env_agree 32 (Ereg regs0 []) E').
{ split; [|rewrite HD; reflexivity].
intros n Hn. rewrite (HA n ltac:(lia)). unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
split; [|split].
- destruct (frame_chunk (ss_mem ss) (fst MIDLEN)) as [e|] eqn:Fc; [|discriminate HMl]. apply sv_eqb_eq in HMl. subst e.
pose proof (frame_chunk_val H E' ss ms (fst MIDLEN) (snd MIDLEN) HS Fc) as V.
rewrite (HA 2%nat ltac:(lia)) in V. unfold MIDLEN in V |- *. cbn [fst snd sv_denot] in V |- *.
rewrite (HA 36%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned in V. exact V.
- exact (regs_chk_ok 32 (Ereg regs0 []) E' H ss ms PAREGS HS HE0 HMr).
- exact (frames_chk_ok 32 (Ereg regs0 []) E' H ss ms PAFRAMES HS HE0 ltac:(lia) HMf).
Qed.
End c.
