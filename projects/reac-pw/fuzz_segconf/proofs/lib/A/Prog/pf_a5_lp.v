(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 781 of its 834 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A5 of reac_segconf_parse_file's walk, the strip_comment
   loop (segment A5's proof, 2026-10-30):
     a5_loop_ok : forall n, H_C B n -> forall k, H_L B k n            (the points of lib/A/Prog/pf_a5_d.v)
   proves no function by itself (segment lemma of reac_segconf_parse_file; its rule-24 record, reuse verdict none,
   is the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md).
   The code (strip_comment inlined, the unit's internal record, commit dfb49d6ad789, path records/segp/
   dis/reac_segconf_parse_file.fuzz_segconf.asan.s; a0 = a1 = buf + k, a3 = -k,
   s2 = '#', a7 = ';', s4 = ' ', a6 = '\t', s6 = SHADOW_OFF):
     0x87eb4 L    check 4 on a1 (load1 at buf + k), lbu a2,0(a0); '#' or ';' -> 0x87ed8; NUL -> 0x87f3c (C);
                  else 0x87efc: a0++, a1++, a3--, back to L
     0x87ed8 M    beqz a3 (k = 0) -> 0x87f24 (a0 = slot 0xb8 = buf); else check 5 (load1 at buf + k - 1),
                  lbu a2,-1(a0); ' ' or '\t' -> 0x87f28; else 0x87efc
     0x87f28 F28  check 6 (store1 at a0 = buf + k), sb zero,0(a0), 0x87f3c (C)
   The proof, in the form of the trim walk's trim_tr.v / trim_l.v (a loop re-seeded at each iteration, the token
   executor deciding the inline checks): one fresh seed per point (lp_seed at L and M, ls_ss at F28); the byte at
   buf + k (atom 32), the byte at buf + k - 1 (atom 33) and slot 0xb8's value buf (atom 34) are extra atoms;
   checks 4 and 5 are obligations discharged from buf's zero shadow (pf_fsh at PF_SC_LINE); check 6 is covered by
   the shadow entry of the stored byte. lp_iter is one iteration, lp_mark the path from a mark, lp_store the cut;
   a5_loop_ok is the induction on the bytes left. The plain proof of the same loop: the plain-build walk owner's
   lib/Prog/pf_p2.v `loop` / `at_e9c` at 04f2be60e018. No Section hypothesis: the steps keep every byte off
   buf (pf_a5_k.v's a5_move0, a5_keep_fsh, a5_keep_ln, a5_keep_slot). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaSB PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The loop's own points (listing offsets; BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition A5_M : Z := AF_reac_segconf_parse_file + 0x460.     (* 0x87ed8, a mark at k: `beqz a3` *)
Definition A5_F28 : Z := AF_reac_segconf_parse_file + 0x4b0.   (* 0x87f28, check 6 and the cut's store *)
(* the registers no instruction of the loop writes (only a0 .. a5 change) *)
Definition LP_KEPT : list Z := [2; 3; 4; 8; 9; 16; 17; 18; 19; 20; 21; 22; 24; 26; 27].

(** ** The symbolic states *)
(* L and M: every register its own atom; atom 32 the byte at buf + k, atom 33 the byte at buf + k - 1, atom 34 buf
   (slot 0xb8, PF_SL); two read-only regions: [buf + k - 1, buf + k + 1) on a0 and slot 0xb8 on s1 *)
Definition lp_r10 : YP09.region :=
  YP09.mkRegion (Some 10%nat) (-1) 1 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 33 0)); YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition lp_r9 : YP09.region := YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0 0 [YP09.mkChunk 0xb8 (CVal 8 (SOff 34 0))].
Definition lp_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] [] [].
Definition lp_ss (pc : Z) : sstate := mkSS pc sr_atoms [lp_r10; lp_r9] None lp_facts.
(* the shadow base of the inline checks: s6 *)
Definition lp_Bx : sv := SOff 22 0.
(* F28: the byte at a0 = buf + k, written; its shadow entry covers check 6 *)
Definition ls_r10 : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition ls_facts : facts := mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0) ] [] [].
Definition ls_ss : sstate := mkSS A5_F28 sr_atoms [ls_r10] None ls_facts.
Definition ls_SH : list shent := [mkSHE 10 0 1].

(** ** Pure helpers *)
Lemma lp_nth_zs : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. reflexivity.
- assert (i = length s) as -> by lia. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma lp_mark_nz : forall c, is_mark c = true -> c <> 0.
Proof. intros c H ->. unfold is_mark in H. cbn in H. discriminate H. Qed.
Lemma lp_U_neg : forall E n k, ew E n = Z_to_bv 64 (- Z.of_nat k) -> (k < 512)%nat ->
  (U E (SOff n 0) =? U E (SLit 0)) = (k =? 0)%nat.
Proof.
intros E n k H Hk. rewrite U_SOff, H, (U_lit E 0) by lia. rewrite Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_0_r, Z.mod_mod by lia.
destruct k as [|k'].
- reflexivity.
- rewrite Z.mod_opp_l_nz by (try rewrite Z.mod_small by lia; lia). rewrite Z.mod_small by lia.
  change ((S k' =? 0)%nat) with false. apply Z.eqb_neq. lia.
Qed.
Lemma lp_br_eq : forall E a b x y c, U E a = x -> U E b = y ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = c -> (x =? y) = c.
Proof. intros E a b x y c Ha Hb H. rewrite branch_eq_U, Ha, Hb in H. exact H. Qed.
Lemma lp_ag_ew : forall E0 E (n : nat) v, env_agree 35 E0 E -> (n < 35)%nat -> ew E0 n = Z_to_bv 64 v ->
  ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma lp_U : forall E0 E (n : nat) v, env_agree 35 E0 E -> (n < 35)%nat -> ew E0 n = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros E0 E n v H Hn H0 Hv. apply U_atom; [exact (lp_ag_ew E0 E n v H Hn H0) | exact Hv]. Qed.
Lemma lp_ag32 : forall rX extra E0 E, env_agree 32 (Ereg rX extra) E0 -> env_agree 35 E0 E ->
  env_agree 32 (Ereg rX extra) E.
Proof.
intros rX extra E0 E [A0 D0] [A1 D1]. split.
- intros n Hn. rewrite (A1 n ltac:(lia)). exact (A0 n Hn).
- rewrite D1. exact D0.
Qed.
Lemma lp_rg_keep : forall (rX rX' : bvmap 5 word) (L : list (Z * Z)) (ks : list Z), pf_rg rX L ->
  Forall (fun rv => In (fst rv) ks) L -> (forall r, In r ks -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_rg rX' L.
Proof.
intros rX rX' L ks H Hin K. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hrv.
rewrite (K _ (Hin rv Hrv)). exact (H rv Hrv).
Qed.
Lemma lp_zs_keep : forall (rd rd' : reader) p l, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) -> 0 <= p ->
  p + Z.of_nat (length l) <= 2 ^ 64 -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros rd rd' p l K H0 H1 H i Hi. rewrite K by lia. exact (H i Hi). Qed.

Ltac lp_in := solve [unfold PF_RL, PF_RM, PF_SL, a5_FI, LP_KEPT; cbn [In app];
  repeat (first [left; reflexivity | right])].
Ltac lp_fst := unfold PF_RL, PF_RM, a5_FI; repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst]; lp_in.
Ltac lp_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The environment of the seeds at L and M *)
Definition lp_extra (v : pfv) (pos C C' : Z) : list word := [Z_to_bv 64 C; Z_to_bv 64 C'; Z_to_bv 64 (a5_buf v pos)].
Definition lp_E (rX : bvmap 5 word) (v : pfv) (pos C C' : Z) : env := Eimg (Ereg rX (lp_extra v pos C C')).
Lemma lp_E_agree : forall rX v pos C C', env_agree 32 (Ereg rX (lp_extra v pos C C')) (lp_E rX v pos C C').
Proof. intros rX v pos C C'. split; [|reflexivity]. intros n Hn. unfold lp_E. apply Eimg_low. unfold A_TEXT. lia. Qed.
Lemma lp_ew_reg : forall rX v pos C C' k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (lp_E rX v pos C C') k = getr rX r.
Proof. intros rX v pos C C' k r Hk. unfold lp_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma lp_ew_x : forall rX v pos C C',
  ew (lp_E rX v pos C C') 32 = Z_to_bv 64 C /\ ew (lp_E rX v pos C C') 33 = Z_to_bv 64 C' /\
  ew (lp_E rX v pos C C') 34 = Z_to_bv 64 (a5_buf v pos).
Proof.
intros rX v pos C C'. unfold lp_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra rX _ 0)|]. split; [exact (ew_Ereg_extra rX _ 1) | exact (ew_Ereg_extra rX _ 2)].
Qed.

(* one byte of the reader as a one-byte chunk (pf_a7_q.v's a7q_val_mem1, segment A7's proof) *)
Lemma lp_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma lp_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) a z,
  aview SEGS H mem a = Some z -> 0 <= z < 256 -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Hv Hz k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem a z Hv) as (b & Hb & Hvb & _).
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Hvb.
symmetry. apply lp_byte_self.
Qed.
(* the byte a run wrote into a one-byte written region (trim_t.v's tr_wbyte, the trim walk) *)
Lemma lp_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
(* the registers a run leaves as their own atoms keep the seed's values *)
Lemma lp_regs_kept : forall rX extra E ss (H : word -> bool) ms (l : list Z),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg rX extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) l) = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros rX extra E ss H ms l HS HA Hl k Hk.
exact (regs_kept_of_st_ok_pi E ss (restrict H ms) rX extra (map (Z_to_bv 5) l) HS HA Hl (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

(* the current point as cfg_at *)
Ltac lp_at pc := lazymatch goal with |- SRr ?sg ?W (mkCfg (mkst ?rg _ ?mm _) ?mdn) ?Q =>
  change (SRr sg W (cfg_at sg (BASE + pc) rg mm mdn) Q) end.
(* after a run that writes nothing: the environment agrees with E0 below 35 (HAE), the reader is the one of the
   seed's memory m0 (KM), every visible byte stays visible (KV); trim_tr.v's tt_after *)
Ltac lp_after W0 m0 E0 HAE KM KV :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?mp) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?mp) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KVn := fresh "KVn" in
    assert (HAEn : env_agree 35 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W0) (ms_mem msn) a = aview SEGS (w_H W0) m0 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ (w_H W0) mp (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KVn : forall a, aview SEGS (w_H W0) m0 a <> None -> aview SEGS (w_H W0) (ms_mem msn) a <> None)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (aview_keeps_vis SEGS _ _ _ a HG (KV a Ha)));
    clear HFr HG HAE KM KV; rename HAEn into HAE; rename KMn into KM; rename KVn into KV;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(** ** buf is addressable at a cut with buf in scope (pf_fsh PF_SC_LINE: cells SH + 8 .. SH + 71 are 0) *)
Lemma lp_ra : forall v pos lyc Sc Wc rX memc mdc, pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  range_addressable (rdW Wc memc) SHADOW_OFF (a5_buf v pos) 512.
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
destruct HB as (_ & _ & _ & _ & HFSH).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
assert (HF8 : pf_F v pos = 8 * (pf_F v pos / 8)).
{ pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)). lia. }
assert (D : (pf_F v pos + 64) / 8 = pf_F v pos / 8 + 8).
{ replace (pf_F v pos + 64) with (pf_F v pos + 8 * 8) by lia. apply Z.div_add. lia. }
apply zero_shadow_range.
- unfold a5_buf, PF_O_BUF. rewrite HF8. replace (8 * (pf_F v pos / 8) + 64) with ((pf_F v pos / 8 + 8) * 8) by lia.
  apply Z_mod_mult.
- reflexivity.
- intros i Hi. change (512 / 8) with 64 in Hi. unfold shadow_of_addr, a5_buf, PF_O_BUF.
  replace (SHADOW_OFF + (pf_F v pos + 64) / 8 + i) with (pf_SH v pos + (8 + i)) by (rewrite D, G10; lia).
  rewrite (HFSH (8 + i) ltac:(lia)), a5_shb_in by lia. reflexivity.
Qed.

(** ** The bytes at buf + k and buf + k - 1 at L k *)
Lemma lp_bytes : forall k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  exists C', rdW Wc memc (a5_buf v pos + Z.of_nat k) = Some (nth k (pf_line (p_s v) o) 0) /\
    0 <= nth k (pf_line (p_s v) o) 0 < 256 /\
    rdW Wc memc (a5_buf v pos + Z.of_nat k - 1) = Some C' /\ 0 <= C' < 256 /\
    ((0 < k)%nat -> C' = nth (k - 1) (pf_line (p_s v) o) 0).
Proof.
intros k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (HB & _ & _ & H512 & HZS & Hk & _ & _).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & HFP & _).
unfold a5_len in *.
pose proof (lp_nth_zs _ _ _ k HZS Hk) as V0.
destruct (aview_byte SEGS (w_H Wc) memc _ _ V0) as (_ & _ & _ & R0).
assert (HP1 : apresent (w_H Wc) memc (a5_buf v pos + Z.of_nat k - 1)) by (apply HFP; unfold a5_buf, PF_O_BUF; lia).
pose proof (aview_some_of_apresent SEGS _ _ _ HP1) as HN1.
destruct (rdW Wc memc (a5_buf v pos + Z.of_nat k - 1)) as [C'|] eqn:V1; [|exfalso; exact (HN1 eq_refl)].
destruct (aview_byte SEGS (w_H Wc) memc _ _ V1) as (_ & _ & _ & R1).
exists C'. split; [exact V0|]. split; [exact R0|]. split; [first [exact V1 | reflexivity]|]. split; [exact R1|].
intros Hk0. pose proof (lp_nth_zs _ _ _ (k - 1) HZS ltac:(lia)) as V2.
replace (a5_buf v pos + Z.of_nat (k - 1)) with (a5_buf v pos + Z.of_nat k - 1) in V2 by lia.
rewrite V1 in V2. injection V2 as ->. reflexivity.
Qed.

(** ** The registers of the seed at L k *)
Lemma lp_env : forall k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C',
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ew (lp_E rX v pos C C') 10 = w64 (a5_buf v pos + Z.of_nat k) /\
  ew (lp_E rX v pos C C') 11 = w64 (a5_buf v pos + Z.of_nat k) /\
  ew (lp_E rX v pos C C') 13 = w64 (- Z.of_nat k) /\ ew (lp_E rX v pos C C') 16 = w64 9 /\
  ew (lp_E rX v pos C C') 17 = w64 0x3b /\ ew (lp_E rX v pos C C') 18 = w64 0x23 /\
  ew (lp_E rX v pos C C') 20 = w64 0x20 /\ ew (lp_E rX v pos C C') 22 = w64 SHADOW_OFF /\
  ew (lp_E rX v pos C C') 9 = w64 (pf_s1 v).
Proof.
intros k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
split; [rewrite (lp_ew_reg rX v pos C C' 10 (Z_to_bv 5 10) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 11 (Z_to_bv 5 11) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 13 (Z_to_bv 5 13) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 16 (Z_to_bv 5 16) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 17 (Z_to_bv 5 17) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 18 (Z_to_bv 5 18) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 20 (Z_to_bv 5 20) eq_refl); eapply a5_rg_get; [exact HRG | lp_in]|].
split; [rewrite (lp_ew_reg rX v pos C C' 22 (Z_to_bv 5 22) eq_refl); eapply a5_rg_get; [exact HFI | lp_in]|].
rewrite (lp_ew_reg rX v pos C C' 9 (Z_to_bv 5 9) eq_refl); eapply a5_rg_get; [exact HFI | lp_in].
Qed.

(** ** The seed at L and M *)
Lemma lp_seed : forall k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' pc,
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  rdW Wc memc (a5_buf v pos + Z.of_nat k) = Some C -> 0 <= C < 256 ->
  rdW Wc memc (a5_buf v pos + Z.of_nat k - 1) = Some C' -> 0 <= C' < 256 ->
  st_ok_pi SEGS VAL (lp_E rX v pos C C') (lp_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' pc HI VC RC VC' RC'.
pose proof HI as (HB & _ & _ & H512 & _ & Hk & _).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & HFP & _).
pose proof (lp_env k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' HI)
  as (E10 & E11 & _ & _ & _ & _ & _ & E22 & E9).
destruct (lp_ew_x rX v pos C C') as (E32 & E33 & E34).
destruct HB as (_ & _ & _ & HSL & _).
assert (HB8 : rdword (rdW Wc memc) (pf_s1 v + 0xb8) = Some (pf_F v pos + PF_O_BUF))
  by exact (proj1 (Forall_forall _ _) HSL (0xb8, pf_F v pos + PF_O_BUF) ltac:(lp_in)).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
unfold a5_len in *.
assert (U9 : bv_unsigned (ew (lp_E rX v pos C C') 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (lp_E rX v pos C C') 10) = a5_buf v pos + Z.of_nat k)
  by (rewrite E10; unfold w64; apply unsigned_lit_small; unfold a5_buf, PF_O_BUF; lia).
assert (U11 : bv_unsigned (ew (lp_E rX v pos C C') 11) = a5_buf v pos + Z.of_nat k)
  by (rewrite E11; unfold w64; apply unsigned_lit_small; unfold a5_buf, PF_O_BUF; lia).
assert (U22 : bv_unsigned (ew (lp_E rX v pos C C') 22) = SB)
  by (rewrite E22; unfold w64, SB; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (lp_E rX v pos C C') 32) = C) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (lp_E rX v pos C C') 33) = C') by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (lp_E rX v pos C C') 34) = a5_buf v pos)
  by (rewrite E34; apply unsigned_lit_small; unfold a5_buf, PF_O_BUF; lia).
rewrite restrict_mkst_fx. unfold lp_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, lp_r10.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. unfold a5_buf, PF_O_BUF in *. split; [lia|]. split; [lia|]. split; [intros o' Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS _ _ _ (-1) 1%N (SOff 33 0) C').
      -- cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      -- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      -- lia.
      -- apply lp_val_mem1; [|exact RC']. replace (pf_F v pos + 64 + Z.of_nat k + -1) with (pf_F v pos + 64 + Z.of_nat k - 1) by lia.
         exact VC'.
    * apply (chunk_ok_val SEGS _ _ _ 0 1%N (SOff 32 0) C).
      -- cbn [sv_denot]. rewrite E32, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      -- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      -- lia.
      -- apply lp_val_mem1; [|exact RC]. rewrite Z.add_0_r. exact VC.
  + unfold region_ok, lp_r9.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o' Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ _ 0xb8 8%N (SOff 34 0) (pf_F v pos + PF_O_BUF)).
    * cbn [sv_denot]. rewrite E34, unsigned_lit_small by (unfold a5_buf, PF_O_BUF; lia). rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_BUF. lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HB8).
- unfold lp_r10, lp_r9. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U10, U9. unfold a5_buf, PF_O_BUF.
  repeat split; lia.
- split; [|split; exact I].
  cbn [lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U11, U22, U32, U33, U34. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold a5_buf, PF_O_BUF, SB.
  repeat split; lia.
Qed.

(** ** The cut facts after a step that writes nothing of the state but (at most) buf *)
Lemma lp_move : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> a5_ln n v pos (rdW Wc memc) cf cur nm o ln d ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos false false a -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc') cf cur nm o ln d /\
  pf_sl (rdW Wc memc') (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)].
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HB HLN HSL HJ' HK HV HRG.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & _ & _ & Hc).
assert (HKt : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha Hn. apply HK; [exact Ha|]. intros Hw. apply Hn. exact (a5_Wrx_mono v pos false false a Hw). }
pose proof HB as (_ & _ & _ & _ & HFSH).
split; [|split].
- apply (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ').
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact HKt.
  + exact HV.
  + exact HRG.
  + exact (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc memc') false PF_SC_LINE G HK HFSH).
- exact (a5_keep_ln B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HKt n cf cur nm o ln d Hc HLN).
- exact (a5_keep_slot v pos (rdW Wc memc) (rdW Wc memc') false _ G HK HSL).
Qed.

(* the register list of a point from the one at L k, the loop's kept registers and the new ones *)
Lemma lp_rl_keep : forall v pos o ln k (rX rX' : bvmap 5 word) T,
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, 0x20); (10, a5_buf v pos + Z.of_nat k); (11, a5_buf v pos + Z.of_nat k); (13, - Z.of_nat k);
             (16, 9); (17, 0x3b)]) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_rg rX' T -> pf_rg rX' (PF_RL v pos ++ PF_RM v o ln ++ T) /\ getr rX' (Z_to_bv 5 20) = w64 0x20 /\
  getr rX' (Z_to_bv 5 16) = w64 9 /\ getr rX' (Z_to_bv 5 17) = w64 0x3b.
Proof.
intros v pos o ln k rX rX' T HRG KR HT.
assert (HRL : pf_rg rX (PF_RL v pos)) by (unfold pf_rg in *; rewrite !Forall_app in HRG; exact (proj1 HRG)).
assert (HRM : pf_rg rX (PF_RM v o ln)) by (unfold pf_rg in *; rewrite !Forall_app in HRG; exact (proj1 (proj2 HRG))).
split; [|split; [|split]].
- unfold pf_rg. rewrite !Forall_app. split; [|split; [|exact HT]].
  + exact (lp_rg_keep rX rX' _ LP_KEPT HRL ltac:(lp_fst) KR).
  + exact (lp_rg_keep rX rX' _ LP_KEPT HRM ltac:(lp_fst) KR).
- rewrite (KR 20) by lp_in. eapply a5_rg_get; [exact HRG | lp_in].
- rewrite (KR 16) by lp_in. eapply a5_rg_get; [exact HRG | lp_in].
- rewrite (KR 17) by lp_in. eapply a5_rg_get; [exact HRG | lp_in].
Qed.

(** ** L k' after a run from L k or M k that wrote nothing *)
Lemma lp_L_move : forall k k' n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  (k' <= a5_len v o)%nat -> (forall j, (j < k')%nat -> r_comment_at (pf_line (p_s v) o) j = false) ->
  getr rX' (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat k') ->
  getr rX' (Z_to_bv 5 11) = w64 (a5_buf v pos + Z.of_nat k') ->
  getr rX' (Z_to_bv 5 13) = w64 (- Z.of_nat k') ->
  INV_L B k' n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros k k' n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM KV KR Hk' HNC' R10 R11 R13.
pose proof HI as (HB & HLN & HSL & H512 & HZS & Hk & HNC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (lp_move n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HB HLN HSL HJ'
  (fun a Ha _ => KM a Ha) KV (lp_rg_keep rX rX' _ LP_KEPT HFI ltac:(lp_fst) KR)) as (HB' & HLN' & HSL').
assert (HT : pf_rg rX' [(10, a5_buf v pos + Z.of_nat k'); (11, a5_buf v pos + Z.of_nat k'); (13, - Z.of_nat k')]).
{ unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption. }
destruct (lp_rl_keep v pos o ln k rX rX' _ HRG KR HT) as (HR1 & R20 & R16 & R17).
refine (conj HB' (conj HLN' (conj HSL' (conj H512 (conj _ (conj Hk' (conj HNC' _))))))).
- unfold a5_len in *. apply (lp_zs_keep _ _ _ _ KM); [unfold a5_buf, PF_O_BUF; lia | |exact HZS].
  rewrite length_app. cbn [length]. unfold a5_buf, PF_O_BUF. lia.
- unfold pf_rg in *. rewrite !Forall_app in HR1 |- *. destruct HR1 as (HR1 & HR2 & _).
  split; [exact HR1|]. split; [exact HR2|].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption.
Qed.

(** ** F28: check 6 and the cut's store at buf + k (a comment starts at k) *)
Definition lp_F28 (k n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\ (a5_len v o < 512)%nat /\
  sa_zs (rdW Wc memc) (a5_buf v pos) (pf_line (p_s v) o ++ [0]) /\ (k < a5_len v o)%nat /\
  r_strip_comment (pf_line (p_s v) o) = firstn k (pf_line (p_s v) o) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (10, a5_buf v pos + Z.of_nat k)]).

Lemma lp_F28_of_L : forall k k' n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  (k' < a5_len v o)%nat -> r_strip_comment (pf_line (p_s v) o) = firstn k' (pf_line (p_s v) o) ->
  getr rX' (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat k') ->
  lp_F28 k' n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros k k' n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM KV KR Hk' HSC R10.
pose proof HI as (HB & HLN & HSL & H512 & HZS & Hk & HNC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (lp_move n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HB HLN HSL HJ'
  (fun a Ha _ => KM a Ha) KV (lp_rg_keep rX rX' _ LP_KEPT HFI ltac:(lp_fst) KR)) as (HB' & HLN' & HSL').
assert (HT : pf_rg rX' [(10, a5_buf v pos + Z.of_nat k')]).
{ unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption. }
destruct (lp_rl_keep v pos o ln k rX rX' _ HRG KR HT) as (HR1 & R20 & R16 & R17).
refine (conj HB' (conj HLN' (conj HSL' (conj H512 (conj _ (conj Hk' (conj HSC _))))))).
- unfold a5_len in *. apply (lp_zs_keep _ _ _ _ KM); [unfold a5_buf, PF_O_BUF; lia | |exact HZS].
  rewrite length_app. cbn [length]. unfold a5_buf, PF_O_BUF. lia.
- unfold pf_rg in *. rewrite !Forall_app in HR1 |- *. destruct HR1 as (HR1 & HR2 & _).
  split; [exact HR1|]. split; [exact HR2|].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption.
Qed.

(** ** C after a run from L k that met the NUL (k = |line|, no comment in the line) *)
Lemma lp_C_of_L : forall k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  k = a5_len v o ->
  INV_C B n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM KV KR Hkl.
pose proof HI as (HB & HLN & HSL & H512 & HZS & Hk & HNC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NZ & _).
pose proof (L_line_bytes_holds (p_s v) o NZ) as (_ & NZl & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold a5_len in *.
assert (HSC : r_strip_comment (pf_line (p_s v) o) = pf_line (p_s v) o).
{ rewrite (r_strip_comment_at (pf_line (p_s v) o) k NZl ltac:(lia) HNC ltac:(intros; lia)), Hkl.
  apply firstn_all. }
destruct (lp_move n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HB HLN HSL HJ'
  (fun a Ha _ => KM a Ha) KV (lp_rg_keep rX rX' _ LP_KEPT HFI ltac:(lp_fst) KR)) as (HB' & HLN' & HSL').
assert (HT : pf_rg rX' [(20, 0x20)]).
{ unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  rewrite (KR 20) by lp_in. eapply a5_rg_get; [exact HRG | lp_in]. }
destruct (lp_rl_keep v pos o ln k rX rX' _ HRG KR HT) as (HR1 & _).
refine (conj HB' (conj HLN' (conj HSL' (conj H512 (conj _ HR1))))).
rewrite HSC. apply (lp_zs_keep _ _ _ _ KM); [unfold a5_buf, PF_O_BUF; lia | |exact HZS].
rewrite length_app. cbn [length]. unfold a5_buf, PF_O_BUF. lia.
Qed.

(** ** F28 -> C: check 6, `sb zero,0(a0)`; buf then holds firstn k line and its NUL *)
Lemma lp_store : forall n, H_C B n -> forall k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  lp_F28 k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_F28) rX memc mdc) (a5_post B v cf cur nm o ln).
Proof.
intros n HC k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HF.
pose proof HF as (HB & HLN & HSL & H512 & HZS & Hk & HSC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lp_ra v pos lyc Sc Wc rX memc mdc HB) as HRA.
unfold a5_len in *.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat k)) by (eapply a5_rg_get; [exact HRG | lp_in]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF) by (eapply a5_rg_get; [exact HFI | lp_in]).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by (apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX []) (Eimg (Ereg rX []))).
{ split; [|reflexivity]. intros i Hi. apply Eimg_low. unfold A_TEXT. lia. }
assert (E10 : ew (Eimg (Ereg rX [])) 10 = w64 (a5_buf v pos + Z.of_nat k))
  by (rewrite (ew_Eimg_Ereg_nat rX [] 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E22 : ew (Eimg (Ereg rX [])) 22 = w64 SHADOW_OFF)
  by (rewrite (ew_Eimg_Ereg_nat rX [] 22 (Z_to_bv 5 22) eq_refl); exact R22).
assert (U10 : bv_unsigned (ew (Eimg (Ereg rX [])) 10) = a5_buf v pos + Z.of_nat k)
  by (rewrite E10; unfold w64; apply unsigned_lit_small; unfold a5_buf, PF_O_BUF; lia).
assert (U22 : bv_unsigned (ew (Eimg (Ereg rX [])) 22) = SB)
  by (rewrite E22; unfold w64, SB; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) ls_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + A5_F28)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ls_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, ls_r10.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. unfold a5_buf, PF_O_BUF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o' Ho. apply (apresent_writable SEGS). apply HFP. lia.
  - cbn. tauto.
  - split; [|split; exact I].
    cbn [ls_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U22. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold a5_buf, PF_O_BUF, SB. repeat split; lia. }
assert (UB : U (Eimg (Ereg rX [])) lp_Bx = SHADOW_OFF)
  by (unfold lp_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; lia]).
assert (UE : U (Eimg (Ereg rX [])) (SOff 10 0) = a5_buf v pos + Z.of_nat k)
  by (apply U_atom; [exact E10 | unfold a5_buf, PF_O_BUF; lia]).
assert (SHOK : sh_ok SEGS lp_Bx ls_SH (Eimg (Ereg rX [])) (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, ls_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H Wc) memc _ lp_Bx 10%nat (a5_buf v pos) 512 (a5_buf v pos + Z.of_nat k) 0 1
    HRA UB UE); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold a5_buf, PF_O_BUF, SHADOW_OFF in *. lia. }
revert HS HEI HA0 E10 E22 U10 U22 UB UE SHOK. generalize (Eimg (Ereg rX [])) as E0.
intros E0 HS HEI HA0 E10 E22 U10 U22 UB UE SHOK.
pose proof (env_agree_refl 35 E0) as HAE.
unfold cfg_at. change (w64 (BASE + A5_F28)) with (Z_to_bv 64 (BASE + A5_F28)).
(* 0x87f28 .. 0x87f38: check 6, the store; up to C *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_C.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U10 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
  unfold a5_buf, PF_O_BUF in Ha. lia. }
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with
| HSn : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?mp) (mrestrict _ (ms_mem ?msn)),
  HG : mem_grows (mrestrict _ ?mp) (mrestrict _ (ms_mem ?msn)) |- _ =>
  assert (KMw : forall a, 0 <= a < 2 ^ 64 -> a <> a5_buf v pos + Z.of_nat k -> rdW Wc (ms_mem msn) a = rdW Wc memc a);
  [ intros a Ha Hne;
    apply (kept_of_frame (segs := SEGS) Eo _ (w_H Wc) memc (ms_mem msn) (fun a' => a' = a5_buf v pos + Z.of_nat k) HFr);
    [|exact Ha | exact Hne];
    intros b wlo whi a' Hin' Hrr; vm_compute in Hin';
    destruct Hin' as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U10 in Hrr; lia
  | ];
  assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem msn) a <> None)
    by (intros a Ha; exact (aview_keeps_vis SEGS _ _ _ a HG Ha));
  assert (HW0 : rdW Wc (ms_mem msn) (a5_buf v pos + Z.of_nat k) = Some 0);
  [ rewrite (lp_wbyte En _ msn (w_H Wc) 10%nat 0%nat (a5_buf v pos + Z.of_nat k) (SLit 0) HSn
      ltac:(vm_compute; reflexivity)); [reflexivity | exact U10]
  | ];
  pose proof (lp_regs_kept rX [] En _ _ msn LP_KEPT HSn (lp_ag32 rX [] E0 En HA0 ltac:(env_agree_chain HAE))
    ltac:(vm_compute; reflexivity)) as HK
end.
pmkst HS. lp_at A5_C.
eapply (HC v pos lyc Sc Wc _ _ _ cf cur nm o ln d).
destruct (lp_move n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d _ _ _ HB HLN HSL HJ
  ltac:(intros a Ha Hn; apply KMw; [exact Ha | intros ->; apply Hn; right; right; left; lia])
  KV (lp_rg_keep rX _ _ LP_KEPT HFI ltac:(lp_fst) HK)) as (HB' & HLN' & HSL').
refine (conj HB' (conj HLN' (conj HSL' (conj H512 (conj _ _))))).
- rewrite HSC. intros i Hi. rewrite length_app, length_firstn in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
  + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec i k) as [_|]; [|lia].
    rewrite KMw by (unfold a5_buf, PF_O_BUF; lia).
    rewrite (HZS i ltac:(rewrite length_app; cbn [length]; lia)). rewrite app_nth1 by lia. reflexivity.
  + assert (i = k) as -> by lia.
    rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (k - Nat.min k (length (pf_line (p_s v) o)))%nat with 0%nat by lia. cbn [nth]. exact HW0.
- unfold pf_rg. rewrite !Forall_app. unfold pf_rg in HRG. rewrite !Forall_app in HRG.
  destruct HRG as (HR1 & HR2 & HR3).
  split; [exact (lp_rg_keep rX _ _ LP_KEPT HR1 ltac:(lp_fst) HK)|].
  split; [exact (lp_rg_keep rX _ _ LP_KEPT HR2 ltac:(lp_fst) HK)|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  rewrite (HK 20) by lp_in. exact (a5_rg_get rX _ 20 _ HR3 ltac:(left; reflexivity)).
Qed.

(** ** M: a mark at k (0x87ed8): the cut at 0x87f28, or no cut and the next iteration *)
Lemma lp_mark : forall n, H_C B n -> forall k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  is_mark (nth k (pf_line (p_s v) o) 0) = true ->
  ((k < a5_len v o)%nat -> forall rX' memc' mdc', INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX' memc' mdc') (a5_post B v cf cur nm o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_M) rX memc mdc) (a5_post B v cf cur nm o ln).
Proof.
intros n HC k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI HMK NEXT.
pose proof HI as (HB & HLN & HSL & H512 & HZS & Hk & HNC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NZ & _).
pose proof (L_line_bytes_holds (p_s v) o NZ) as (_ & NZl & _).
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lp_ra v pos lyc Sc Wc rX memc mdc HB) as HRA.
destruct (lp_bytes k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI) as (C' & VC & RC & VC' & RC' & EC').
set (C := nth k (pf_line (p_s v) o) 0) in *.
unfold a5_len in *.
assert (Hkl : (k < length (pf_line (p_s v) o))%nat).
{ destruct (Nat.lt_ge_cases k (length (pf_line (p_s v) o))) as [H|H]; [exact H|].
  exfalso. apply (lp_mark_nz C HMK). unfold C. apply nth_overflow. exact H. }
pose proof (lp_seed k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' A5_M HI VC RC VC' RC') as HS.
pose proof (lp_env k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' HI)
  as (E10 & E11 & E13 & E16 & E17 & E18 & E20 & E22 & E9).
destruct (lp_ew_x rX v pos C C') as (E32 & E33 & E34).
pose proof (lp_E_agree rX v pos C C') as HA0.
assert (HEI : img_env VAL A_LIM (lp_E rX v pos C C')) by (apply Eimg_env).
revert HS HEI HA0 E10 E11 E13 E16 E17 E18 E20 E22 E9 E32 E33 E34.
generalize (lp_E rX v pos C C') as E0.
intros E0 HS HEI HA0 E10 E11 E13 E16 E17 E18 E20 E22 E9 E32 E33 E34.
pose proof (env_agree_refl 35 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros; assumption).
assert (SHOK : sh_ok SEGS lp_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
assert (UB : U E0 lp_Bx = SHADOW_OFF) by (unfold lp_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; lia]).
(* the exits to F28 (the cut at k) and to L (k + 1) *)
assert (TOF : forall rX' memc' mdc', r_comment_at (pf_line (p_s v) o) k = true ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat k) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_F28) rX' memc' mdc') (a5_post B v cf cur nm o ln)).
{ intros rX' memc' mdc' Hca HJ' KM' KV' KR' R10'.
  apply (lp_store n HC k v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d).
  apply (lp_F28_of_L k k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM' KV' KR' Hkl);
    [|exact R10'].
  exact (r_strip_comment_at (pf_line (p_s v) o) k NZl ltac:(lia) HNC (fun _ => Hca)). }
assert (TOL : forall rX' memc' mdc', r_comment_at (pf_line (p_s v) o) k = false ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat (S k)) ->
  getr rX' (Z_to_bv 5 11) = w64 (a5_buf v pos + Z.of_nat (S k)) ->
  getr rX' (Z_to_bv 5 13) = w64 (- Z.of_nat (S k)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX' memc' mdc') (a5_post B v cf cur nm o ln)).
{ intros rX' memc' mdc' Hca HJ' KM' KV' KR' R10' R11' R13'.
  apply (NEXT Hkl rX' memc' mdc').
  apply (lp_L_move k (S k) n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM' KV' KR');
    [unfold a5_len; lia | | exact R10' | exact R11' | exact R13'].
  intros j Hj. destruct (Nat.eq_dec j k) as [->|Hne]; [exact Hca | apply HNC; lia]. }
clear NEXT.
unfold cfg_at. change (w64 (BASE + A5_M)) with (Z_to_bv 64 (BASE + A5_M)).
(* 0x87ed8 beqz a3 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* k = 0: 0x87f24 a0 = slot 0xb8 = buf; the cut at 0 *)
  rewrite branch_eq_U, (lp_U_neg E0 13 k E13 ltac:(lia)) in Hc. apply Nat.eqb_eq in Hc. subst k.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_F28. { lp_awr. }
  lp_after Wc memc E0 HAE KM KV.
  pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  prreg HS (Z_to_bv 5 10) N10. rewrite E34 in N10.
  pmkst HS. lp_at A5_F28.
  apply (TOF _ _ _); [| exact HJ | exact KM | exact KV | exact HK | rewrite N10; unfold w64; f_equal; lia].
  unfold r_comment_at. fold C. rewrite HMK. reflexivity.
- (* k <> 0: check 5, the byte at buf + k - 1 *)
  rewrite branch_eq_U, (lp_U_neg E0 13 k E13 ltac:(lia)) in Hc. apply Nat.eqb_neq in Hc. rename Hc into Hk0.
  pose proof (EC' ltac:(lia)) as EC.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_F28.
  { cbn [ms_mem]. rewrite (U_atom_off E0 11 (a5_buf v pos + Z.of_nat k) (-1) E11) by (unfold a5_buf, PF_O_BUF; lia).
    apply (obl_of_range SEGS (w_H Wc) memc E0 lp_Bx _ 1 (a5_buf v pos) 512 HRA UB); lia. }
  { lp_awr. }
  lp_after Wc memc E0 HAE KM KV.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the byte before is ' ': the cut at k *)
    pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 33 _ HAE ltac:(lia) E33 ltac:(lia)) (lp_U _ _ 20 32 HAE ltac:(lia) E20 ltac:(lia)) Hc)
      as Hp. apply Z.eqb_eq in Hp. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_F28. { lp_awr. }
    lp_after Wc memc E0 HAE KM KV.
    pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    prreg HS (Z_to_bv 5 10) N10. rewrite E10 in N10.
    pmkst HS. lp_at A5_F28.
    apply (TOF _ _ _); [| exact HJ | exact KM | exact KV | exact HK | exact N10].
    unfold r_comment_at. fold C. rewrite HMK, <- EC, Hp. destruct (k =? 0)%nat; reflexivity.
  + pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 33 _ HAE ltac:(lia) E33 ltac:(lia)) (lp_U _ _ 20 32 HAE ltac:(lia) E20 ltac:(lia)) Hc)
      as Hp. apply Z.eqb_neq in Hp. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_F28. { lp_awr. }
    lp_after Wc memc E0 HAE KM KV.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* the byte before is '\t': the cut at k *)
      pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 33 _ HAE ltac:(lia) E33 ltac:(lia)) (lp_U _ _ 16 9 HAE ltac:(lia) E16 ltac:(lia)) Hc)
        as Ht. apply Z.eqb_eq in Ht. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_F28. { lp_awr. }
      lp_after Wc memc E0 HAE KM KV.
      pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      prreg HS (Z_to_bv 5 10) N10. rewrite E10 in N10.
      pmkst HS. lp_at A5_F28.
      apply (TOF _ _ _); [| exact HJ | exact KM | exact KV | exact HK | exact N10].
      unfold r_comment_at. fold C. rewrite HMK, <- EC, Ht. destruct (k =? 0)%nat; reflexivity.
    * (* no blank before the mark: no cut, the next iteration *)
      pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 33 _ HAE ltac:(lia) E33 ltac:(lia)) (lp_U _ _ 16 9 HAE ltac:(lia) E16 ltac:(lia)) Hc)
        as Ht. apply Z.eqb_neq in Ht. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_L. { lp_awr. }
      lp_after Wc memc E0 HAE KM KV.
      pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 13) N13.
      rewrite E10 in N10. rewrite E11 in N11. rewrite E13 in N13. unfold w64 in N10, N11, N13.
      rewrite Lib.Step.unsigned_Z_to_bv_add in N10, N11, N13.
      pmkst HS. lp_at A5_L.
      apply (TOL _ _ _); [| exact HJ | exact KM | exact KV | exact HK
        | rewrite N10; unfold w64; f_equal; lia | rewrite N11; unfold w64; f_equal; lia
        | rewrite N13; unfold w64; f_equal; lia].
      unfold r_comment_at. fold C. rewrite HMK, <- EC.
      replace (k =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      unfold sp_tab. rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Ht). reflexivity.
Qed.

(** ** One iteration at L k *)
Lemma lp_iter : forall n, H_C B n -> forall k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ((k < a5_len v o)%nat -> forall rX' memc' mdc', INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX' memc' mdc') (a5_post B v cf cur nm o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX memc mdc) (a5_post B v cf cur nm o ln).
Proof.
intros n HC k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI NEXT.
pose proof HI as (HB & HLN & HSL & H512 & HZS & Hk & HNC & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NZ & _).
pose proof (L_line_bytes_holds (p_s v) o NZ) as (_ & NZl & _).
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lp_ra v pos lyc Sc Wc rX memc mdc HB) as HRA.
destruct (lp_bytes k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI) as (C' & VC & RC & VC' & RC' & _).
set (C := nth k (pf_line (p_s v) o) 0) in *.
unfold a5_len in *.
pose proof (lp_seed k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' A5_L HI VC RC VC' RC') as HS.
pose proof (lp_env k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d C C' HI)
  as (E10 & E11 & E13 & E16 & E17 & E18 & E20 & E22 & E9).
destruct (lp_ew_x rX v pos C C') as (E32 & E33 & E34).
pose proof (lp_E_agree rX v pos C C') as HA0.
assert (HEI : img_env VAL A_LIM (lp_E rX v pos C C')) by (apply Eimg_env).
revert HS HEI HA0 E10 E11 E13 E16 E17 E18 E20 E22 E9 E32 E33 E34.
generalize (lp_E rX v pos C C') as E0.
intros E0 HS HEI HA0 E10 E11 E13 E16 E17 E18 E20 E22 E9 E32 E33 E34.
pose proof (env_agree_refl 35 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros; assumption).
assert (SHOK : sh_ok SEGS lp_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
assert (UB : U E0 lp_Bx = SHADOW_OFF) by (unfold lp_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; lia]).
(* the exit to M (a mark at k) *)
assert (TOM : forall rX' memc' mdc', is_mark C = true ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r LP_KEPT -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 10) = w64 (a5_buf v pos + Z.of_nat k) ->
  getr rX' (Z_to_bv 5 11) = w64 (a5_buf v pos + Z.of_nat k) ->
  getr rX' (Z_to_bv 5 13) = w64 (- Z.of_nat k) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_M) rX' memc' mdc') (a5_post B v cf cur nm o ln)).
{ intros rX' memc' mdc' HMK HJ' KM' KV' KR' R10' R11' R13'.
  apply (lp_mark n HC k v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d); [| exact HMK | exact NEXT].
  exact (lp_L_move k k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM' KV' KR' Hk HNC
    R10' R11' R13'). }
unfold cfg_at. change (w64 (BASE + A5_L)) with (Z_to_bv 64 (BASE + A5_L)).
(* 0x87eb4 .. 0x87ec8: check 4, the byte, `beq a2,s2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. rewrite (U_atom E0 11 (a5_buf v pos + Z.of_nat k) E11) by (unfold a5_buf, PF_O_BUF; lia).
  apply (obl_of_range SEGS (w_H Wc) memc E0 lp_Bx _ 1 (a5_buf v pos) 512 HRA UB); lia. }
{ lp_awr. }
lp_after Wc memc E0 HAE KM KV.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* '#': M *)
  pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (lp_U _ _ 18 35 HAE ltac:(lia) E18 ltac:(lia)) Hc)
    as Hm. apply Z.eqb_eq in Hm. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_M. { lp_awr. }
  lp_after Wc memc E0 HAE KM KV.
  pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 13) N13.
  rewrite E10 in N10. rewrite E11 in N11. rewrite E13 in N13.
  pmkst HS. lp_at A5_M.
  apply (TOM _ _ _); [unfold is_mark; rewrite Hm; reflexivity | exact HJ | exact KM | exact KV | exact HK
    | exact N10 | exact N11 | exact N13].
- pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (lp_U _ _ 18 35 HAE ltac:(lia) E18 ltac:(lia)) Hc)
    as Hm. apply Z.eqb_neq in Hm. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_M. { lp_awr. }
  lp_after Wc memc E0 HAE KM KV.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* ';': M *)
    pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (lp_U _ _ 17 59 HAE ltac:(lia) E17 ltac:(lia)) Hc)
      as Hs. apply Z.eqb_eq in Hs. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_M. { lp_awr. }
    lp_after Wc memc E0 HAE KM KV.
    pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 13) N13.
    rewrite E10 in N10. rewrite E11 in N11. rewrite E13 in N13.
    pmkst HS. lp_at A5_M.
    apply (TOM _ _ _); [unfold is_mark; rewrite Hs, orb_true_r; reflexivity | exact HJ | exact KM | exact KV
      | exact HK | exact N10 | exact N11 | exact N13].
  + pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (lp_U _ _ 17 59 HAE ltac:(lia) E17 ltac:(lia)) Hc)
      as Hs. apply Z.eqb_neq in Hs. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_C. { lp_awr. }
    lp_after Wc memc E0 HAE KM KV.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* the NUL: k = |line|, C *)
      pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (U_lit _ 0 ltac:(lia)) Hc) as H0.
      apply Z.eqb_eq in H0. clear Hc.
      assert (Hkl : k = length (pf_line (p_s v) o)).
      { destruct (Nat.lt_ge_cases k (length (pf_line (p_s v) o))) as [Hlt|Hge]; [|lia].
        exfalso. apply NZl. rewrite <- H0. unfold C. apply nth_In. exact Hlt. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_C. { lp_awr. }
      lp_after Wc memc E0 HAE KM KV.
      pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      pmkst HS. lp_at A5_C.
      eapply (HC v pos lyc Sc Wc _ _ _ cf cur nm o ln d).
      exact (lp_C_of_L k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d _ _ _ HI HJ KM KV HK Hkl).
    * (* any other byte: no comment at k, the next iteration *)
      pose proof (lp_br_eq _ _ _ _ _ _ (lp_U _ _ 32 _ HAE ltac:(lia) E32 ltac:(lia)) (U_lit _ 0 ltac:(lia)) Hc) as H0.
      apply Z.eqb_neq in H0. clear Hc.
      assert (Hkl : (k < length (pf_line (p_s v) o))%nat).
      { destruct (Nat.lt_ge_cases k (length (pf_line (p_s v) o))) as [Hlt|Hge]; [exact Hlt|].
        exfalso. apply H0. unfold C. apply nth_overflow. exact Hge. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_L. { lp_awr. }
      lp_after Wc memc E0 HAE KM KV.
      pose proof (lp_regs_kept rX (lp_extra v pos C C') _ _ _ _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 13) N13.
      rewrite E10 in N10. rewrite E11 in N11. rewrite E13 in N13. unfold w64 in N10, N11, N13.
      rewrite Lib.Step.unsigned_Z_to_bv_add in N10, N11, N13.
      pmkst HS. lp_at A5_L.
      apply (NEXT Hkl _ _ _).
      apply (lp_L_move k (S k) n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d _ _ _ HI HJ KM KV HK);
        [unfold a5_len; lia | | rewrite N10; unfold w64; f_equal; lia | rewrite N11; unfold w64; f_equal; lia
        | rewrite N13; unfold w64; f_equal; lia].
      intros j Hj. destruct (Nat.eq_dec j k) as [->|Hne]; [|apply HNC; lia].
      unfold r_comment_at. fold C. unfold is_mark.
      rewrite (proj2 (Z.eqb_neq _ _) Hm), (proj2 (Z.eqb_neq _ _) Hs). reflexivity.
Qed.

(** ** The loop: by induction on the bytes of the line left *)
Theorem a5_loop_ok : forall n, H_C B n -> forall k, H_L B k n.
Proof.
intros n HC.
assert (IND : forall j k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, (k + j = a5_len v o)%nat ->
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX memc mdc) (a5_post B v cf cur nm o ln)).
{ induction j as [|j IH]; intros k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d Hkj HI;
    apply (lp_iter n HC k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI);
    intros Hlt rX' memc' mdc' HI'.
  - lia.
  - exact (IH (S k) v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ltac:(lia) HI'). }
intros k. unfold H_L. intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (_ & _ & _ & _ & _ & Hk & _).
exact (IND (a5_len v o - k)%nat k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ltac:(lia) HI).
Qed.

End e.
End f.
End d.
