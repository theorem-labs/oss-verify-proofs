(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/pix_orient_fuzzer/lib/K5/A23/I_strchr.v, with its module paths changed; 396 of its 426 lines of code are new or changed and 83 lines of the source are left out. *)
(* The asan strchr interceptor of fuzz_disco.asan-ubsan, walked instruction by instruction: the exported
   trampoline, the sanitizer's internal strlen, the shadow-byte scan and the region check the interceptor
   runs after REAL(strchr) returns, and the whole interceptor from entry to return.  The proofs take the
   region-is-poisoned contract (rip_stmt) and REAL(strchr)'s contract (chr_stmt) as section hypotheses. *)
(* Statements relocated to libreac/fuzz_disco.asan-ubsan from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_strchrw.v (a working branch 3e35620c52e) by reloc.py (target disco-Y): module paths and 25 address numerals, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv. That file is a Theorem Labs lane's unchanged port from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_strchrw.v. Proofs written anew from the statements. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.A Require Import IcptSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.A Require Import D_kit I_ikit I_tramp.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation ISTRCHR_DEPTH := 2224%Z (only parsing).
Local Notation chr_ms R Fr pc fc mm := (MS R Fr (Z_to_bv 64 pc) fc None mm (seg_rom asegs)) (only parsing).
Lemma tramp_strchr : tramp_step 0x42a48 0x43528.
Proof.
  (* the exported symbol is one jump to the interceptor body *)
  red. intros * Hbody. lstep. exact Hbody.
Qed.
Definition chr_idx (c : Z) (str : list byte) : nat :=
  match find_byte c str with Some i => i | None => length str end.
Definition chr_res (A c : Z) (str : list byte) : Z :=
  match find_byte c str with Some i => A + Z.of_nat i | None => 0 end.
Definition chr_n (A c : Z) (str : list byte) : Z :=
  if chr_res A c str =? 0 then Z.of_nat (length str) + 1 else chr_res A c str - A + 1.
Lemma chr_idx_le : forall c str, (chr_idx c str <= length str)%nat.
Proof.
  intros c str. unfold chr_idx.
  destruct (find_byte c str) as [k|] eqn:Hfind; [| lia].
  destruct (find_byte_Some _ _ _ Hfind) as [Hk _]. lia.
Qed.
Lemma chr_n_ge : forall A c str, Z.of_nat (chr_idx c str) + 1 <= chr_n A c str.
Proof.
  intros A c str. unfold chr_n, chr_res, chr_idx.
  destruct (find_byte c str) as [k|] eqn:Hfind.
  - destruct (find_byte_Some _ _ _ Hfind) as [Hk _].
    destruct (Z.eqb_spec (A + Z.of_nat k) 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.
Lemma chr_n_le : forall A c str, chr_n A c str <= Z.of_nat (length str) + 1.
Proof.
  intros A c str. unfold chr_n, chr_res.
  destruct (find_byte c str) as [k|] eqn:Hfind.
  - destruct (find_byte_Some _ _ _ Hfind) as [Hk _].
    destruct (Z.eqb_spec (A + Z.of_nat k) 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.
(* Rounding [s + a] up to a multiple of 8 is monotone in [a]. *)
Lemma round8_up_mono : forall s a b, a <= b -> a + (- (s + a)) mod 8 <= b + (- (s + b)) mod 8.
Proof.
  intros s a b Hab.
  pose proof (Z.div_mod (- (s + a)) 8 ltac:(lia)) as Da.
  pose proof (Z.div_mod (- (s + b)) 8 ltac:(lia)) as Db.
  pose proof (Z.mod_pos_bound (- (s + a)) 8 ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (- (s + b)) 8 ltac:(lia)) as Rb.
  lia.
Qed.
Lemma pad_mono : forall s x y, x + 1 <= y -> x + 1 + (- (s + x + 1)) mod 8 <= y + (- (s + y)) mod 8.
Proof.
  intros s x y Hxy. replace (s + x + 1) with (s + (x + 1)) by lia.
  apply round8_up_mono. exact Hxy.
Qed.
Lemma pad_mono2 : forall s x y, x <= y -> x + (- (s + x)) mod 8 <= y + (- (s + y)) mod 8.
Proof. intros s x y Hxy. apply round8_up_mono. exact Hxy. Qed.
Lemma nth_firstn_pref : forall (l : list byte) L j, (j < length (firstn L l))%nat -> nth_error (firstn L l) j = nth_error l j.
Proof.
  induction l as [|b l IH]; intros L j Hj.
  - destruct L; cbn in Hj; lia.
  - destruct L as [|L]; cbn in Hj |- *; [lia|].
    destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.
Lemma firstn_cstr : forall (str slack : list byte) L, (length str < L)%nat ->
  firstn L (str ++ Z_to_bv 8 0 :: slack) = str ++ Z_to_bv 8 0 :: firstn (L - S (length str)) slack.
Proof.
  intros str slack L HL.
  rewrite firstn_app, firstn_all2 by lia. f_equal.
  replace (L - length str)%nat with (S (L - S (length str))) by lia.
  reflexivity.
Qed.
Lemma cstr_byte : forall (str rest : list byte) j, ~ In (Z_to_bv 8 0) str -> 0 <= j <= Z.of_nat (length str) ->
  exists b, nth_error (str ++ Z_to_bv 8 0 :: rest) (Z.to_nat j) = Some b /\ (bv_unsigned b = 0 <-> j = Z.of_nat (length str)).
Proof.
  intros str rest j Hnz Hj.
  destruct (Z.eq_dec j (Z.of_nat (length str))) as [Hend|Hmid].
  - (* the terminator itself *)
    exists (Z_to_bv 8 0). split.
    + rewrite nth_error_app2 by lia. replace (Z.to_nat j - length str)%nat with 0%nat by lia. reflexivity.
    + split; intros _; [exact Hend| reflexivity].
  - (* a byte of the string proper, which is never zero *)
    assert (Hlt : (Z.to_nat j < length str)%nat) by lia.
    destruct (nth_error str (Z.to_nat j)) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
    exists b. rewrite nth_error_app1 by exact Hlt. split; [exact Hb|].
    (* b lies in the string, so it is not the zero byte, so its value is not 0 *)
    assert (Hin : In b str) by (eapply nth_error_In; eassumption).
    assert (Hne : b <> Z_to_bv 8 0) by (intros Heq; rewrite Heq in Hin; exact (Hnz Hin)).
    split; intros Hv; [| contradiction].
    apply bv_neq in Hne. change (bv_unsigned (Z_to_bv 8 0)) with 0 in Hne.
    contradiction.
Qed.
Lemma iislen_loop : forall (k : nat) (j s : Z) (str rest : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  Z.of_nat (length str) - j = Z.of_nat k -> 0 <= j -> s + Z.of_nat (length str) + 1 < 2^64 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (chr_ms (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 j) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F 0x645ec fc m).
Proof.
  induction k as [|k IH]; intros j s str rest ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Hleft Hj Hfit Hbytes Hnz Hinv;
    pose proof (bytes_at_bound _ _ _ _ Hbytes) as [Hs0 _].
  - (* j is the terminator's index: the loop reads the zero byte and returns j *)
    assert (Hjl : j = Z.of_nat (length str)) by lia. subst j.
    destruct (cstr_byte str rest (Z.of_nat (length str)) Hnz ltac:(lia)) as (b & Hnth & Hzero).
    pose proof (bytes_at_nth1 asegs m s _ _ b Hbytes Hnth) as Hb1. rewrite Nat2Z.id in Hb1.
    pose proof (ro_C1_of_bytes m _ _ Hb1) as Hcell.
    pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
    assert (Hb0 : bv_unsigned b = 0) by (apply Hzero; reflexivity).
    assert (Us : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (Ul : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str))) = Z.of_nat (length str)) by (apply unsigned_lit; lia).
    assert (Usl : bv_unsigned (Z_to_bv 64 (s + Z.of_nat (length str))) = s + Z.of_nat (length str)) by (apply unsigned_lit; lia).
    lstep. set (q := s + Z.of_nat (length str)) in *. do 3 lstep.
    rewrite Hb0. if_false.
    do 2 lstep.
    apply evt_done. unfold leaf_post. do 14 eexists. exists m.
    split; [| split; [apply munch_refl| split; [apply wmono_refl| exact Hinv]]].
    reflexivity.
  - (* j is inside the string: the byte is nonzero and the loop goes round with j + 1 *)
    destruct (cstr_byte str rest j Hnz ltac:(lia)) as (b & Hnth & Hzero).
    pose proof (bytes_at_nth1 asegs m s _ _ b Hbytes Hnth) as Hb1. rewrite Z2Nat.id in Hb1 by lia.
    pose proof (ro_C1_of_bytes m _ _ Hb1) as Hcell.
    pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
    assert (Hbn : bv_unsigned b <> 0) by (intros Hb; apply Hzero in Hb; lia).
    assert (Us : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (Uj : bv_unsigned (Z_to_bv 64 j) = j) by (apply unsigned_lit; lia).
    assert (Usj : bv_unsigned (Z_to_bv 64 (s + j)) = s + j) by (apply unsigned_lit; lia).
    lstep. set (q := s + j) in *. do 3 lstep.
    if_cases Hc; zify_cond Hc; [| exfalso; rewrite ?unsigned_lit in Hc by lia; lia].
    apply (IH (j + 1) s str rest); [lia| lia| exact Hfit| exact Hbytes| exact Hnz| exact Hinv].
Qed.
Lemma iislen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str rest : list byte),
  a0 = Z_to_bv 64 s -> bytes_at asegs m s (str ++ Z_to_bv 8 0 :: rest) -> s + Z.of_nat (length str) + 1 < 2^64 ->
  ~ In (Z_to_bv 8 0) str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x645e8) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros -> Hbytes Hfit Hnz Hinv.
  (* [mv a1, zero] starts the index at 0; then the loop does the rest *)
  lstep.
  apply (iislen_loop (length str) 0 s str rest); [lia| lia| exact Hfit| exact Hbytes| exact Hnz| exact Hinv].
Qed.
Definition chr_post : word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word ->
    word -> word -> word -> word -> bvmap 5 word -> bv 32 -> word -> word -> list byte -> list byte -> Z -> mem ->
    machine_state -> Prop := fun rra rsp rgp rtp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 fregs fctl pstr pch bs held zlo m0 st =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mr : mem),
    st = MS (mkR rra rsp rgp rtp t0' t1' t2' v0 v1 (Z_to_bv 64 (chr_res (bv_unsigned pstr) (bv_unsigned pch mod 256) bs))
                 a1' a2' a3' a4' a5' a6' a7' v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
            fregs (ret_pc rra) fctl None mr (seg_rom asegs)
    /\ munch [(bv_unsigned rsp - 32, bv_unsigned rsp)] m0 mr /\ wmono asegs m0 mr /\ mem_inv asegs mr
    /\ stk asegs mr zlo (bv_unsigned rsp) /\ bytes_at asegs mr (bv_unsigned pstr) held.
Definition chr_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (str slack full : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) full ->
  (forall j, (j < length full)%nat -> nth_error full j = nth_error (str ++ Z_to_bv 8 0 :: slack) j) ->
  ~ In (Z_to_bv 8 0) str ->
  Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1
    + (- (bv_unsigned a0 + Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1)) mod 8 <= Z.of_nat (length full) ->
  mem_inv asegs m ->
  0 < bv_unsigned a1 mod 256 ->
  lo <= bv_unsigned sp - 32 ->
  (bv_unsigned a0 + Z.of_nat (length full) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0) ->
  bv_unsigned sp <= 2^47 ->
  evt asegs (chr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str full lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a00c) fc None m (seg_rom asegs)).
Definition icells_chr : mem -> Prop := fun mm =>
  ro_cells asegs mm 0xa08a0 [C8 (Z_to_bv 64 0x13afa8)]
  /\ ro_cells asegs mm 0xa08b0 [C8 (Z_to_bv 64 0xa9478)]
  /\ ro_cells asegs mm 0xa9478 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs mm 0xaa158 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs mm 0xa25c0 [C8 (Z_to_bv 64 0x9a00c)]
  /\ ro_cells asegs mm 0x13b09d [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs mm 0x13b0a5 [C1 (Z_to_bv 8 1)].
Lemma istrchr_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = chr_ms (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F 0x4371c fc m)
    (chr_ms (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F 0x4370c fc m).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Hgap Hc He Hcells Hinv;
    destruct (Hcells c ltac:(lia)) as (sb & Hsb);
    pose proof (ro_C1_of_bytes m c sb Hsb) as Hro;
    assert (Uc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia);
    assert (Uc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
  - (* last shadow byte: a1 reaches e and the loop falls through *)
    assert (Hec : e = c + 1) by lia. subst e.
    do 4 lstep. if_false.
    apply evt_done. do 2 eexists. reflexivity.
  - assert (Ue : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    do 4 lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply Hcells; lia| exact Hinv].
Qed.
Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis SC : chr_stmt.
Lemma istrchr_rip :
  forall (spz pz rz : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (spz + -2144) -> lo <= spz - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> spz < 2^63 ->
  0 <= pz -> 0 <= rz -> pz + rz + 1 < 2^63 ->
  acc asegs m pz (rz + 1) -> rng_ok pz (rz + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = chr_ms (mkR ra' (Z_to_bv 64 (spz + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                        s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F 0x4364c fc m'
      /\ munch [(spz - 2224, spz - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (spz + -2144))
    (chr_ms (mkR ra (Z_to_bv 64 (spz + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (rz + 1)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 pz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F 0x43724 fc m).
Proof.
  intros until lo. intros Hstk Hlo Hkh Hsp Hp Hr Hpr Hacc Hrng Hm2s Hinv.
  destruct (Hrng ltac:(lia)) as [Hreg Hsz].
  pose proof (munch_refl [(spz - 2224, spz - 2144)] m) as Hmu.
  pose proof (wmono_refl asegs m) as Hwm.
  assert (Usp : bv_unsigned (Z_to_bv 64 (spz + -2144)) = spz + -2144)
    by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  (* keep a0 in s6, pass (p, size) and call __asan_region_is_poisoned *)
  do 4 lstep.
  pose proof RIP as Hrip. unfold rip_stmt in Hrip.
  call Hrip; [reflexivity| reflexivity| exact Hacc| lia| exact Hreg| exact Hm2s| rewrite Usp; exact Hstk
             | lia| unfold kHighShadowEnd in *; lia| exact Hinv|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Usp in H; rename H into Hstk1 end.
  (* the region is clean: the result 0 sends the walk back to the common exit *)
  do 3 lstep. if_true.
  apply evt_done. eexists. do 21 eexists. split; [reflexivity|].
  split; [exact Hmu|]. split; [exact Hwm|]. split; [assumption| exact Hstk1].
Qed.
(* The aligned shadow word the quick check loads for address [a]. *)
Lemma qc_word_addr : forall a, 0 <= a < 2^63 ->
  Z.land ((2147450880 + a ≫ 3) mod 18446744073709551616) 18446744073709551608 = al8 (shad a).
Proof.
  intros a Ha. unfold al8, shad, SHB.
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (Hq : 0 <= a / 8 < 2^60) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by lia. rewrite land_m8' by lia.
  rewrite (Z.add_comm (a / 8)). reflexivity.
Qed.
Lemma istrchr_chk :
  forall (spz pz rz : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  s0 = Z_to_bv 64 spz ->
  stk asegs m lo (spz + -2144) -> lo <= spz - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> spz < 2^63 ->
  0 <= pz -> 0 <= rz -> pz + rz + 1 < 2^63 ->
  chk_ok m pz (rz + 1) -> m2s_cells m -> ro_cells asegs m 0xa08b0 [C8 (Z_to_bv 64 0xa9478)] ->
  ro_cells asegs m 0xa9478 [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = chr_ms (mkR ra' (Z_to_bv 64 (spz + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                        s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F 0x4364c fc m'
      /\ munch [(spz - 2224, spz - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (spz + -2144))
    (chr_ms (mkR ra (Z_to_bv 64 (spz + -2144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 pz) (Z_to_bv 64 rz) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F 0x435f8 fc m).
Proof.
  intros until lo. intros -> Hstk Hlo Hkh Hsp Hp Hr Hpr (Hacc & Hqc & Hrng) Hm2s Hslot Hbase Hinv.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(spz - 2224, spz - 2144)] m) as Hmu.
  pose proof (wmono_refl asegs m) as Hwm.
  assert (Up : bv_unsigned (Z_to_bv 64 pz) = pz) by (apply unsigned_lit; lia).
  assert (Ur : bv_unsigned (Z_to_bv 64 rz) = rz) by (apply unsigned_lit; lia).
  assert (Ur1 : bv_unsigned (Z_to_bv 64 (rz + 1)) = rz + 1) by (apply unsigned_lit; lia).
  (* size = rz + 1, and the end pointer does not wrap *)
  do 4 lstep. rewrite (lxor_ones64 pz) by lia.
  assert (Unp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - pz)) = 18446744073709551615 - pz)
    by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec rz 64) as [Hsmall|Hbig].
  2:{ (* more than 64 bytes: straight to the full region check *)
      if_true. lstep. if_true.
      apply (istrchr_rip spz pz rz); try assumption; unfold kHighShadowEnd; lia. }
  if_false.
  (* at most 64 bytes: or the two aligned shadow words of the first and the last byte *)
  destruct (Hqc ltac:(lia)) as (wa & wb & Hwa & Hwb).
  replace (pz + (rz + 1) - 1) with (rz + pz) in Hwb by lia.
  do 10 lstep.
  rewrite (qc_word_addr pz), (qc_word_addr (rz + pz)) by lia.
  do 4 lstep.
  if_cases Hzw.
  - (* some shadow is set: test the last byte's granule and scan the bytes before it *)
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    pose proof (acc_shadow_bytes m pz (rz + 1) Hacc ltac:(lia) Hp) as Hsb. unfold shad, SHB in Hsb.
    destruct (Hsb (2147450880 + (rz + pz) / 8)) as (lb & Hlb).
    { replace (pz + (rz + 1) - 1) with (rz + pz) by lia.
      pose proof (Z.div_le_mono pz (rz + pz) 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (ro_C1_of_bytes _ _ _ Hlb) as Hlc.
    pose proof (Z.div_le_mono pz (rz + pz) 8 ltac:(lia) ltac:(lia)) as Hord.
    assert (Hpz8 : 0 <= pz / 8 < 2^60) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (Hrz8 : 0 <= (rz + pz) / 8 < 2^60) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (Uls : bv_unsigned (Z_to_bv 64 (2147450880 + pz / 8)) = 2147450880 + pz / 8) by (apply unsigned_lit; lia).
    assert (Ule : bv_unsigned (Z_to_bv 64 (2147450880 + (rz + pz) / 8)) = 2147450880 + (rz + pz) / 8)
      by (apply unsigned_lit; lia).
    set (ls := 2147450880 + pz / 8) in *. set (le := 2147450880 + (rz + pz) / 8) in *.
    do 7 lstep.
    if_cases Hge; zify_cond Hge;
      [| eapply evt_cut;
         [ eapply (istrchr_loop (Z.to_nat (le - ls - 1)) ls le);
           [ rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
           | lia | lia
           | intros x Hx; apply Hsb; unfold ls, le in Hx; replace (pz + (rz + 1) - 1) with (rz + pz) by lia; lia
           | exact Hinv ]
         | intros ms' (a3' & a4' & ->) ] ].
    (* the verdict byte decides between the common exit and the full region check *)
    all: lstep; lstep; if_cases Hz.
    all: try (apply evt_done; eexists; do 21 eexists; split; [reflexivity|];
              split; [exact Hmu|]; split; [exact Hwm|]; split; [exact Hinv| exact Hstk]).
    all: apply (istrchr_rip spz pz rz); try assumption; unfold kHighShadowEnd; lia.
  - apply evt_done. eexists. do 21 eexists. split; [reflexivity|].
    split; [exact Hmu|]. split; [exact Hwm|]. split; [exact Hinv| exact Hstk].
Qed.
Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRCHR_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
(* The end both outcomes share: s3 holds [rz] and the interceptor reads rz + 1 bytes from [s].  Check that
   range, pop the frame and return.  [m0] is the memory at entry, [Hc0] its range facts, [Hmu0] the frame
   footprint since entry, [Flow] / [Fhigh] the two carved parts of the frame. *)
Local Ltac strchr_finish m0 top s rz Hc0 Hmu0 Flow Fhigh :=
  let Hck := fresh "Hck" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Hck : chk_ok mm s (rz + 1))
      by (apply (chk_ok_agree m0 mm s _ Hc0 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ Hmu0); intros ? ?; cbn [outside]; split; [lia| exact I])
  end;
  call (istrchr_chk top s rz);
    [ reflexivity | eassumption | lia | unfold kHighShadowEnd; lia | lia | lia | lia | lia
    | exact Hck | split; [| split]; assumption | assumption | assumption | assumption | ];
  lazymatch goal with Hst : stk asegs _ _ (top + -2144) |- _ =>
    do 11 lstep;
    release_frame Flow Hst (top + -72); release_frame Fhigh Hst top
  end;
  lstep;
  unfold istrchr_post; sys_finish;
  rewrite (unsigned_lit top) by lia; first [exact Hmu0| eassumption].
Theorem istrchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str slack : list byte) (L : nat) (lo : Z),
  a0 = Z_to_bv 64 s ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= s -> s + Z.of_nat L <= 2^47 ->
  bytes_at asegs m s (firstn L (str ++ Z_to_bv 8 0 :: slack)) -> ~ In (Z_to_bv 8 0) str ->
  (L <= length str + S (length slack))%nat ->
  0 < bv_unsigned a1 mod 256 ->
  chr_n s (bv_unsigned a1 mod 256) str + (- (s + chr_n s (bv_unsigned a1 mod 256) str)) mod 8 <= Z.of_nat L ->
  (s + Z.of_nat L <= bv_unsigned sp - ISTRCHR_DEPTH \/ bv_unsigned sp <= s) ->
  chk_ok m s (chr_n s (bv_unsigned a1 mod 256) str) -> m2s_cells m -> icells_chr m -> mem_inv asegs m ->
  evt asegs (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (chr_res s (bv_unsigned a1 mod 256) str) lo m)
    (chr_ms (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F 0x43528 fc m).
Proof using RIP SC.
  intros until lo. intros -> Hstk Hlo Hkh Hsp Hs Hsl Hbuf Hnz HL Hc Hpad Hsep Hchk Hm2s Hcells Hinv.
  unfold kHighShadowEnd in *.
  set (top := bv_unsigned sp) in *.
  assert (Esp : sp = Z_to_bv 64 top) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite Esp.
  pose proof (munch_refl [(top - 2224, top)] m) as Hmu. pose proof (wmono_refl asegs m) as Hwm.
  destruct Hcells as (Cflags & Cm2s & Cbase & Cinit & Creal & Cstrict & Cuse).
  destruct Hm2s as (M2a & M2b & M2c).
  assert (Utop : bv_unsigned (Z_to_bv 64 top) = top) by (apply unsigned_lit; lia).
  assert (Us : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (Ufr : bv_unsigned (Z_to_bv 64 (top + -2144)) = top + -2144) by (apply unsigned_lit; lia).
  (* the bytes the caller hands over: exactly L of them *)
  assert (Hfull : length (firstn L (str ++ Z_to_bv 8 0 :: slack)) = L)
    by (rewrite length_firstn, length_app; cbn [length]; lia).
  set (full := firstn L (str ++ Z_to_bv 8 0 :: slack)) in *.
  (* prologue: nine saved registers at the top, then the rest of the 2144-byte frame *)
  carve_frame 72%nat Hstk. rename FR into Hsave. carve_frame 2072%nat Hstk.
  do 15 lstep.
  call asan_inited_spec; [exact Cinit| assumption|].
  lstep. if_false. lstep.
  call try_init_spec; [exact Cinit| rewrite Ufr; exact Hstk| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Ufr in H; rename H into Hstk2 end.
  do 6 lstep.
  pose proof SC as Hreal. unfold chr_stmt in Hreal.
  call Hreal;
    [ rewrite Ufr; exact Hstk2
    | rewrite Us; exact Hbuf
    | intros j Hj; unfold full in Hj |- *; apply nth_firstn_pref; exact Hj
    | exact Hnz
    | rewrite Us, Hfull; eapply Z.le_trans; [apply pad_mono; apply (chr_n_ge s)| exact Hpad]
    | assumption
    | exact Hc
    | rewrite Ufr; lia
    | rewrite Us, Ufr, Hfull; lia
    | rewrite Ufr; lia
    | ].
  rewrite Us.
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Ufr in H end.
  set (c := bv_unsigned a1 mod 256) in *.
  (* the interceptor's flags: intercept_strchr is set, strict_string_checks is not *)
  lstep. if_false. do 4 lstep. if_false. do 2 lstep. if_false. lstep.
  pose proof (Z.mod_pos_bound (- (s + chr_n s c str)) 8 ltac:(lia)) as Hpad0.
  destruct (Z.eq_dec (chr_res s c str) 0) as [Hnull|Hhit].
  - (* null result: the interceptor measures the whole string with internal_strlen *)
    assert (Hn : chr_n s c str = Z.of_nat (length str) + 1) by (unfold chr_n; rewrite Hnull; reflexivity).
    assert (Hlt : (length str < L)%nat) by lia.
    pose proof Hbuf as Hcs. unfold full in Hcs. rewrite firstn_cstr in Hcs by exact Hlt.
    rewrite Hnull. if_true.
    do 3 lstep.
    call iislen_spec; [reflexivity| exact Hcs| lia| exact Hnz| assumption|].
    do 2 lstep.
    rewrite Hn in Hchk.
    strchr_finish m top s (Z.of_nat (length str)) Hchk Hmu FR Hsave.
  - (* a hit at index i: the read size is i + 1 *)
    assert (Hidx : exists i, find_byte c str = Some i).
    { unfold chr_res in Hhit. destruct (find_byte c str) as [i|]; [exists i; reflexivity| congruence]. }
    destruct Hidx as (i & Hf).
    destruct (find_byte_Some _ _ _ Hf) as [Hi _].
    assert (Hres : chr_res s c str = s + Z.of_nat i) by (unfold chr_res; rewrite Hf; reflexivity).
    assert (Hn : chr_n s c str = Z.of_nat i + 1)
      by (unfold chr_n; destruct (Z.eqb_spec (chr_res s c str) 0); [contradiction| lia]).
    assert (Ures : bv_unsigned (Z_to_bv 64 (s + Z.of_nat i)) = s + Z.of_nat i) by (apply unsigned_lit; lia).
    rewrite Hres in Hhit |- *. if_false.
    do 2 lstep.
    replace (s + Z.of_nat i - s) with (Z.of_nat i) by lia.
    rewrite Hn in Hchk.
    strchr_finish m top s (Z.of_nat i) Hchk Hmu FR Hsave.
Qed.
End WithRIP.
