(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0qn X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Definition seq_post {RCEIL : RunCeiling} (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 nw xw s0v rav : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (st : mstate) (m : mem) : machine_state -> Prop :=
fun ms' => exists (a1 a4 a5 : word) junk' m',
ms' = MS (mkR (Z_to_bv 64 0x16dc0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 nw s1
xw a1 xw (Z_to_bv 64 CTX) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 alloc_meta_entry) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CTX + 848, CTX + 880); (CTX + 912, CTX + 913)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 (Z_to_bv 64 CTX); C8 a7; C8 xw; CB 24 junk'; C8 s0v; C8 rav]
/\ mrep (step_seq st) m'.

Ltac raw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame asegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write asegs mX _ _ A bs') in ST; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
apply (wmono_write asegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv asegs mX |- _ =>
apply (mem_inv_store asegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qe.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1rl.

Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.

Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
upd_ctx (set_mmap_counter v)
(put_meta g (big_meta rid n)
(put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).

Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Lemma zeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
(forall o, 0 <= o < Z.of_nat k -> bytes_at asegs m (x + o) [b8 0]) -> bytes_at asegs m x (zeros k).
Proof.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. exact HB.
Qed.

Lemma cell_read_hdr_havoc_fresh : forall st b o,
(s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

Lemma big_word_eq rid n : 0 <= n < 2^32 ->
Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + 4115))) 12))) 12))) 4064)
= wz (meta_word (big_meta rid n)).
Proof.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
rewrite (unsigned_lit (n + 4115)) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit ((n + 4115) / 2 ^ 12)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2 by lia.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia). change (2 ^ 12) with 4096.
rewrite (X1rl.lor_add _ _ 12); [| lia| lia| change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia].
unfold wz. f_equal. lia.
Qed.

Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma ctr_word c : 0 <= c -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv c)) + 1)) = wz (sxv (u32 (c + 1))).
Proof.
intros Hc. rewrite addw_word. rewrite wz_unsigned by apply sxv_range. f_equal. apply sxv_congr.
unfold u32. rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_sxv v : le4 (wz (sxv v)) = le4 (wz v).
Proof.
apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply X0qm.mod_mod_pow2. lia.
Qed.

Section SUCC.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

End SUCC.

