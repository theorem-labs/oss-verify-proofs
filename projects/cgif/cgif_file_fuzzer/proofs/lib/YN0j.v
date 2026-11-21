(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's CONFIG_RSEQ flag): changed R_auxp, R_auxv, mem_am0, F_sh, F_av, facts_am0, ss_am0, ss_i1 and 9 more; added AUXV_ALL, AUXV_ALL_span, AUXV_ALL_claimed, AUXV_ALL_OFF, AUXV_ALL_r, R_auxv_of, R_auxv_t, R_auxv_f and 13 more. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a YO0c YN2e YN2j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition LOCK : Z := src0_D_malloc_lock.
Definition CTX : Z := src0_D_malloc_context.
Definition LIBC : Z := src0_D_libc.
Definition TP : Z := src0_tp.
Definition ERRNO : Z := src0_tp - 164.
Definition GOT : Z := src0_D_got_stack_chk_guard.
Definition GUARD : Z := src0_D_stack_chk_guard.
Definition AMS : Z := 160.
Definition PC_MCRET : Z := src0_A_alloc_meta + 0x7c.
Definition PC_A2 : Z := src0_A_alloc_meta + 0xa4.
Definition PC_V : Z := src0_A_alloc_meta + 0x1b8.
Definition PC_GRET : Z := src0_A_alloc_meta + 0x18c.
Definition PC_O : Z := src0_A_alloc_meta + 0x218.
Definition PC_RET : Z := src0_A_alloc_meta + 0x2a4.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition addR (r : region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition resume_ (ss : sstate) (rv : sv) (rs : smem) : sstate := mkSS (ss_pc ss + 4) (sr_set (ss_regs ss) 10 rv) rs None (ss_facts ss).
Definition setmem (rs : smem) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss).
Definition setfacts (G : facts) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) G.
Definition setpc (pc : Z) (ss : sstate) : sstate := mkSS pc (ss_regs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Fixpoint lupd_nth {A} (l : list A) (i : nat) (f : A -> A) : list A :=
match l, i with
| [], _ => []
| x :: l', O => f x :: l'
| x :: l', S i' => x :: lupd_nth l' i' f
end.
Definition upd_chunk (i : nat) (off : Z) (cv : cval) (ss : sstate) : sstate :=
setmem (lupd_nth (ss_mem ss) i (fun r =>
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r)
(map (fun c => if Z.eqb (c_off c) off then mkChunk off cv else c) (r_chunks r)))) ss.
Definition drop_chunk (i : nat) (off : Z) (ss : sstate) : sstate :=
setmem (lupd_nth (ss_mem ss) i (fun r =>
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (List.filter (fun c => negb (Z.eqb (c_off c) off)) (r_chunks r)))) ss.
Definition regs_am : list sv :=
SLit 0 :: SOff 1 0 :: SOff 2 0 :: SOff 3 0 :: SLit TP :: map (fun r => SOff r 0) (seq 5 27).
Definition R_stack : region := mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0 [].
Definition R_got : region := mkRegion None GOT (GOT + 8) 0 0 [mkChunk GOT (CVal 8 (SLit GUARD))].
Definition R_guard : region := mkRegion None GUARD (GUARD + 8) 0 0 [mkChunk GUARD (CVal 8 (SOff 32 0))].
Definition R_pgsz : region := mkRegion None (LIBC + 48) (LIBC + 56) 0 0 [mkChunk (LIBC + 48) (CVal 8 (SLit 4096))].
Definition R_errno : region := mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [].
Definition R_ctxA (i : bool) : region :=
mkRegion None CTX (CTX + 12) CTX (CTX + 12)
[mkChunk CTX (CVal 8 (if i then SOff 0 0 else SLit 0)); mkChunk (CTX + 8) (CVal 4 (SLit (if i then 1 else 0)))].
Definition R_ctxB : region :=
mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 16) (CVal 8 (SOff 33 0)); mkChunk (CTX + 24) (CVal 8 (SOff 36 0));
mkChunk (CTX + 32) (CVal 8 (SOff 37 0)); mkChunk (CTX + 40) (CVal 8 (SOff 38 0));
mkChunk (CTX + 48) (CVal 8 (SOff 39 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0));
mkChunk (CTX + 64) (CVal 8 (SOff 41 0)); mkChunk (CTX + 72) (CVal 8 (SOff 42 0))].
Definition R_ctxC : region :=
mkRegion None (CTX + 920) (CTX + 928) (CTX + 920) (CTX + 928) [mkChunk (CTX + 920) (CVal 8 (SOff 43 0))].
Definition R_auxp : region := mkRegion None (LIBC + 8) (LIBC + 16) 0 0 [mkChunk (LIBC + 8) (CVal 8 (SOff 44 0))].
(* EVERY pair's KEY word, pair index 0..28, in the order
   [StackLayout.auxv_entries] lists them (LPS 75d69e00,
   theories/LinuxProcessSem/StackLayout.v:231-262, read at [la_rseq = true]),
   then AT_RANDOM's VALUE word, in ascending offset order.

   WHY NOT THE CLAIM TABLE.  This was generated from [AUXV_CLAIMED] ([YO0d],
   which takes it from [YK09.APC]) and that table is the nine pairs whose
   VALUE a plan variable denotes, plus AT_NULL — a deliberate SUBSET of the
   vector.  It covered the whole vector only by accident of the pre-revision
   layout, where the vector WAS ten pairs spanning [0,160) with keys at
   0,16,..,144 and AT_RANDOM's value at 136, so subset and vector coincided.
   At the revision the vector is twenty-nine pairs ([auxv_count true = 29],
   StackLayout.v:276) and nineteen of them are unclaimed, so nineteen key
   words had no chunk.  musl's [get_random_secret] walks the vector from pair
   0 and stops at the first zero key, reading every key on the way, so the
   first unclaimed key is an unresolvable load: [run_am0] stopped with
   [RS_stopped (SR_load (Some 44%nat) 0)] at pair 0 instead of reaching
   [memcpy].  A KEY needs no plan variable — it is a literal of
   [auxv_entries] — so claiming all twenty-nine costs nothing the plan has to
   supply, and the VALUE words stay unclaimed exactly as before.

   [AUXV_ALL_span] and [AUXV_ALL_claimed] are the drift guards: the first
   fails if the vector's length stops agreeing with [AUXV_SPAN], the second
   if a claimed pair's index or type stops agreeing with this list. *)
Definition AUXV_ALL : list (Z * Z) :=
[(0, 33); (1, 40); (2, 41); (3, 42); (4, 43); (5, 44); (6, 45); (7, 46); (8, 47); (9, 51);
(10, 16); (11, 6); (12, 17); (13, 3); (14, 4); (15, 5); (16, 7); (17, 8); (18, 9);
(19, 11); (20, 12); (21, 13); (22, 14); (23, 23); (24, 25); (25, 31); (26, 27); (27, 28); (28, 0)].
Lemma AUXV_ALL_span : 16 * Z.of_nat (length AUXV_ALL) = AUXV_SPAN.
Proof. rewrite auxv_span_val. vm_compute. reflexivity. Qed.
Lemma AUXV_ALL_claimed :
map (fun p => (fst p, nth (Z.to_nat (fst p)) (map snd AUXV_ALL) 0)) AUXV_CLAIMED = AUXV_CLAIMED.
Proof. vm_compute. reflexivity. Qed.
(* The rseq-off vector: pairs 0..25 as above, AT_NULL at 26 ([YO0d.AUXV_TYPES_OFF]). *)
Definition AUXV_ALL_OFF : list (Z * Z) := firstn 26 AUXV_ALL ++ [(26, 0)].
Definition AUXV_ALL_r (rs : bool) : list (Z * Z) := if rs then AUXV_ALL else AUXV_ALL_OFF.
Definition R_auxv_of (rs : bool) : region :=
mkRegion (Some 44%nat) 0 (AUXV_SPAN_r rs) 0 0
(map (fun p => mkChunk (16 * fst p) (CVal 8 (SLit (snd p)))) (firstn 25 (AUXV_ALL_r rs))
++ mkChunk AT_RANDOM_VOFF (CVal 8 (SOff 45 0))
:: map (fun p => mkChunk (16 * fst p) (CVal 8 (SLit (snd p)))) (skipn 25 (AUXV_ALL_r rs))).
Definition R_auxv_t : region := Eval vm_compute in R_auxv_of true.
Definition R_auxv_f : region := Eval vm_compute in R_auxv_of false.
Definition R_auxv (rs : bool) : region := if rs then R_auxv_t else R_auxv_f.
Definition R_fh : region := mkRegion (Some 33%nat) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff 35 0)); mkChunk 8 (CVal 8 (SOff 34 0))].
Definition R_nx : region := mkRegion (Some 34%nat) 0 8 0 8 [].
Definition R_pr : region := mkRegion (Some 35%nat) 8 16 8 16 [].
Definition R_am : region := mkRegion (Some 36%nat) 0 16 0 16 [].
Definition R_tl : region := mkRegion (Some 41%nat) 8 16 8 16 [].
Definition zregion (n : nat) (off len : Z) : region :=
mkRegion (Some n) off (off + len) off (off + len) [mkChunk off (CZero len)].
Definition mem_am1 : smem := [R_stack; R_got; R_guard; R_pgsz; R_ctxA true; R_ctxB; R_ctxC; R_errno].
Definition mem_am0 (rs : bool) : smem := [R_stack; R_got; R_guard; R_pgsz; R_ctxA false; R_ctxB; R_ctxC; R_errno; R_auxp; R_auxv rs].
Definition F_sp : afact := mkAF (CEIL_MIN + AMS) (2 ^ 63 - 1) 4.
Definition F_sh : afact := mkAF 0 40 0.
(* the auxv's whole extent at the run's flag.  [auxv_check] reads this as
   [af_hi + AUXV_SPAN_r rs <=? 2 ^ 63], so the two are one number and
   [F_av_hi_of_AUXV_SPAN] below fails if they stop being. *)
Definition F_av (rs : bool) : afact := mkAF 4096 (2 ^ 63 - AUXV_SPAN_r rs) 0.
Lemma F_av_hi_of_AUXV_SPAN : forall rs, af_hi (F_av rs) + AUXV_SPAN_r rs = 2 ^ 63.
Proof. intros rs. unfold F_av. cbn [af_hi]. lia. Qed.
Definition F_ar : afact := mkAF 4096 (2 ^ 63 - 16) 0.
Definition F_pg : afact := mkAF 4096 (CEIL_MAX - 4096) 12.
Definition facts_am1 : facts := mkFacts [ (2%nat, F_sp); (39%nat, F_sh) ] [] [].
Definition facts_am0 (rs : bool) : facts := mkFacts [ (2%nat, F_sp); (39%nat, F_sh); (44%nat, F_av rs); (45%nat, F_ar) ] [] [].
Definition ss_am1 : sstate := mkSS src0_A_alloc_meta regs_am mem_am1 None facts_am1.
Definition ss_am0 (rs : bool) : sstate := mkSS src0_A_alloc_meta regs_am (mem_am0 rs) None (facts_am0 rs).
(* The walk to get_random_secret's memcpy reads every key of the vector, so it is one run
   per flag; the two runs meet again at [ss_A2] ([merge_a2y]). *)
Definition ss_i1_t : sstate := Eval vm_compute in runto_ src0_A_memcpy (ss_am0 true).
Definition ss_i1_f : sstate := Eval vm_compute in runto_ src0_A_memcpy (ss_am0 false).
Definition ss_i1 (rs : bool) : sstate := if rs then ss_i1_t else ss_i1_f.
Definition MC_JUNK : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition mem_i2_of (ss : sstate) : smem :=
match store_region (ss_mem ss) (Some 2%nat) (-64) 8 (CVal 8 (SOff 0 0)) with Some rs => rs | None => [] end.
Definition mem_i2_t : smem := Eval vm_compute in mem_i2_of ss_i1_t.
Definition mem_i2_f : smem := Eval vm_compute in mem_i2_of ss_i1_f.
Definition mem_i2 (rs : bool) : smem := if rs then mem_i2_t else mem_i2_f.
Definition ss_i1' (rs : bool) : sstate := setpc PC_MCRET (setmem (mem_i2 rs) (ss_i1 rs)).
Definition ss_i2_t : sstate := Eval vm_compute in junk_regs MC_JUNK 46 (ss_i1' true).
Definition ss_i2_f : sstate := Eval vm_compute in junk_regs MC_JUNK 46 (ss_i1' false).
Definition ss_i2 (rs : bool) : sstate := if rs then ss_i2_t else ss_i2_f.
Definition ss_a2x : sstate := Eval vm_compute in runto_ PC_A2 ss_am1.
Definition ss_a2y_t : sstate := Eval vm_compute in runto_ PC_A2 ss_i2_t.
Definition ss_a2y_f : sstate := Eval vm_compute in runto_ PC_A2 ss_i2_f.
Definition ss_a2y (rs : bool) : sstate := if rs then ss_a2y_t else ss_a2y_f.
Definition A2_JUNK : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 28]%bv.
Definition ss_A2 : sstate := Eval vm_compute in junk_regs A2_JUNK 57 ss_a2x.
Definition C_fh0 : acond := mkAC BC_EQ (SOff 33 0) (SLit 0).
Definition C_fh1 : acond := mkAC BC_NE (SOff 33 0) (SLit 0).
Definition C_amc1 : acond := mkAC BC_NE (SOff 37 0) (SLit 0).
Definition C_amc0 : acond := mkAC BC_EQ (SOff 37 0) (SLit 0).
Definition C_nxm : acond := mkAC BC_EQ (SOff 34 0) (SOff 33 0).
Definition C_nxo : acond := mkAC BC_NE (SOff 34 0) (SOff 33 0).
Definition ss_fh : sstate := Eval vm_compute in run_ ss_A2.
Definition ss_amc : sstate := Eval vm_compute in run_ (add_cond ss_fh C_fh0).
Definition ss_c1 : sstate := Eval vm_compute in run_ (add_cond ss_amc C_amc1).
Definition ss_c2 : sstate := addR R_am ss_c1.
Definition ss_cE : sstate := Eval vm_compute in run_ ss_c2.
Definition ss_d0 : sstate := addR R_fh (add_cond ss_fh C_fh1).
Definition ss_d1 : sstate := Eval vm_compute in run_ ss_d0.
Definition ss_d1E : sstate := Eval vm_compute in run_ (add_cond ss_d1 C_nxm).
Definition ss_d2 : sstate := addR R_pr (addR R_nx (add_cond ss_d1 C_nxo)).
Definition ss_d2E : sstate := Eval vm_compute in run_ ss_d2.
Definition C_aac1 : acond := mkAC BC_NE (SOff 38 0) (SLit 0).
Definition C_aac0 : acond := mkAC BC_EQ (SOff 38 0) (SLit 0).
Definition C_bd : acond := mkAC BC_EQ (SOff 43 0) (SLit (2 ^ 64 - 1)).
Definition C_nbd : acond := mkAC BC_NE (SOff 43 0) (SLit (2 ^ 64 - 1)).
Definition C_bn : acond := mkAC BC_EQ (SOff 43 0) (SLit 0).
Definition C_bc : acond := mkAC BC_NE (SOff 43 0) (SLit 0).
Definition ss_aac : sstate := Eval vm_compute in run_ (add_cond ss_amc C_amc0).
Definition ss_r0 : sstate := add_atom (add_cond ss_aac C_aac1) 42 F_pg.
Definition ss_rK : sstate := Eval vm_compute in run_ ss_r0.
Definition ss_b0 : sstate := Eval vm_compute in run_ (add_cond ss_aac C_aac0).
Definition ss_b1 : sstate := Eval vm_compute in run_ (add_cond ss_b0 C_nbd).
Definition ss_vBD : sstate := Eval vm_compute in runto_ PC_V (add_cond ss_b0 C_bd).
Definition ss_nQ : sstate := Eval vm_compute in run_ (add_cond ss_b1 C_bn).
Definition ss_nQ1 : sstate := add_atom (resume_ ss_nQ (SOff 72 0) (ss_mem ss_nQ)) 72 F_pg.
Definition ss_nG : sstate := Eval vm_compute in run_ ss_nQ1.
Definition ss_nR : sstate := resume_ ss_nG (SOff 72 0) (ss_mem ss_nG).
Definition ss_vBN : sstate := Eval vm_compute in runto_ PC_V ss_nR.
Definition ss_cG : sstate := Eval vm_compute in run_ (add_cond ss_b1 C_bc).
Definition ss_cR : sstate := resume_ ss_cG (SOff 43 0) (ss_mem ss_cG).
Definition ss_vBC : sstate := Eval vm_compute in runto_ PC_V ss_cR.
Definition V_JUNK : list reg := [9; 12; 17]%bv.
Definition facts_V : facts := mkFacts [ (2%nat, F_sp); (39%nat, F_sh) ] [C_aac0; C_amc0; C_fh0] [].
Definition absV (ss : sstate) : sstate := upd_chunk 6 (CTX + 920) (CVal 8 (SLit (2 ^ 64 - 1))) (junk_regs V_JUNK 74 ss).
Definition ss_V : sstate := Eval vm_compute in setfacts facts_V (absV ss_vBD).
Definition F_n2 : afact := mkAF 2 (2 ^ 41) 1.
Definition F_nl : afact := mkAF 8192 (2 ^ 53) 12.
Definition ss_v1 : sstate := Eval vm_compute in runto_ (src0_A_alloc_meta + 0x1c4) ss_V.
Definition ss_v1' : sstate := add_atom (junk_regs [9%bv] 77 ss_v1) 77 F_n2.
Definition ss_v2 : sstate := Eval vm_compute in runto_ (src0_A_alloc_meta + 0x1c8) ss_v1'.
Definition ss_v2' : sstate := add_atom (junk_regs [11%bv] 78 ss_v2) 78 F_nl.
Definition ss_vK : sstate := Eval vm_compute in run_ ss_v2'.
Definition ss_vF1 : sstate := resume_ ss_vK (SLit (2 ^ 64 - 12)) (ss_mem ss_vK).
Definition ss_vF1E : sstate := Eval vm_compute in run_ ss_vF1.
Definition ss_vG : sstate := add_atom (resume_ ss_vK (SOff 79 0) (ss_mem ss_vK)) 79 F_pg.
Definition ss_vG1 : sstate := Eval vm_compute in run_ ss_vG.
Definition C_vok : acond := mkAC BC_NE (SAlu ALU_OR (SLit 0) (SAlu ALU_XOR (SOff 79 0) (SLit (-1)))) (SLit 0).
Definition ss_vK2 : sstate := Eval vm_compute in run_ (add_cond ss_vG1 C_vok).
Definition ss_vF2 : sstate := resume_ ss_vK2 (SLit (2 ^ 64 - 12)) (ss_mem ss_vK2).
Definition ss_vF2E : sstate := Eval vm_compute in run_ ss_vF2.
Definition ss_vO : sstate := resume_ ss_vK2 (SLit 0) (ss_mem ss_vK2).
Definition ss_oV : sstate := Eval vm_compute in runto_ PC_O ss_vO.
Definition ss_rF : sstate := resume_ ss_rK (SLit (2 ^ 64 - 12)) (ss_mem ss_rK).
Definition ss_rFE : sstate := Eval vm_compute in run_ ss_rF.
Definition ss_rO : sstate := resume_ ss_rK (SLit 0) (ss_mem ss_rK).
Definition ss_oR : sstate := Eval vm_compute in runto_ PC_O ss_rO.
Definition ss_nGG : sstate := resume_ ss_nG (SOff 72 8192) (ss_mem ss_nG).
Definition ss_nK3 : sstate := Eval vm_compute in run_ ss_nGG.
Definition C_gok1 : acond := mkAC BC_NE (SAlu ALU_OR (SOff 72 0) (SLit 11)) (SLit 0).
Definition C_gok2 : acond := mkAC BC_NE (SAlu ALU_OR (SOff 72 0) (SAlu ALU_XOR (SOff 72 0) (SLit (-1)))) (SLit 0).
Definition ss_g1 : sstate := Eval vm_compute in run_ (resume_ ss_nK3 (SLit (2 ^ 64 - 12)) (ss_mem ss_nK3)).
Definition ss_oN1 : sstate := Eval vm_compute in runto_ PC_O (add_cond ss_g1 C_gok1).
Definition ss_g2 : sstate := Eval vm_compute in run_ (resume_ ss_nK3 (SOff 72 0) (ss_mem ss_nK3)).
Definition ss_oN2 : sstate := Eval vm_compute in runto_ PC_O (add_cond ss_g2 C_gok2).
Definition ss_cGG : sstate := resume_ ss_cG (SOff 43 4096) (ss_mem ss_cG).
Definition ss_oC : sstate := Eval vm_compute in runto_ PC_O ss_cGG.
Definition O_JUNK : list reg := [1; 5; 8; 10; 11; 12; 13; 14; 15; 16; 17; 20]%bv.
Definition absO (ss : sstate) : sstate :=
upd_chunk 6 (CTX + 920) (CVal 8 (SOff 110 0))
(upd_chunk 5 (CTX + 48) (CVal 8 (SOff 109 0))
(upd_chunk 5 (CTX + 40) (CVal 8 (SOff 108 0))
(junk_regs O_JUNK 96 (junk_regs [9%bv] 95 ss)))).
Definition facts_O : facts := mkFacts [ (95%nat, F_pg); (2%nat, F_sp); (39%nat, F_sh) ] [C_amc0; C_fh0] [].
Definition ss_O' : sstate := Eval vm_compute in setfacts facts_O (drop_chunk 5 (CTX + 72) (absO ss_oC)).
Definition R_page : region := zregion 95 0 4096.
Definition ss_O : sstate := addR R_page ss_O'.
Definition C_tl0 : acond := mkAC BC_EQ (SOff 41 0) (SLit 0).
Definition C_tl1 : acond := mkAC BC_NE (SOff 41 0) (SLit 0).
Definition ss_o1 : sstate := Eval vm_compute in run_ ss_O.
Definition ss_oE0 : sstate := Eval vm_compute in run_ (add_cond ss_o1 C_tl0).
Definition ss_o2 : sstate := addR R_tl (add_cond ss_o1 C_tl1).
Definition ss_oE1 : sstate := Eval vm_compute in run_ ss_o2.
Lemma run_am0 : forall rs, sym_run_toN src0segs src0tbl FUEL src0_A_memcpy (ss_am0 rs) = (ss_i1 rs, RS_running).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma store_i1 : forall rs, store_region (ss_mem (ss_i1 rs)) (Some 2%nat) (-64) 8 (CVal 8 (SOff 0 0)) = Some (mem_i2 rs).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma run_i2 : forall rs, sym_run_toN src0segs src0tbl FUEL PC_A2 (ss_i2 rs) = (ss_a2y rs, RS_running).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma run_am1 : sym_run_toN src0segs src0tbl FUEL PC_A2 ss_am1 = (ss_a2x, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_A2 : sym_runN src0segs src0tbl FUEL ss_A2 = (ss_fh, RS_stopped (SR_branch BC_EQ (SOff 33 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_fh0 : sym_runN src0segs src0tbl FUEL (add_cond ss_fh C_fh0) = (ss_amc, RS_stopped (SR_branch BC_EQ (SOff 37 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_amc1 : sym_runN src0segs src0tbl FUEL (add_cond ss_amc C_amc1) = (ss_c1, RS_stopped (SR_store (Some 36%nat) 8)).
Proof. vm_compute. reflexivity. Qed.
Lemma run_c2 : sym_runN src0segs src0tbl FUEL ss_c2 = (ss_cE, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_d0 : sym_runN src0segs src0tbl FUEL ss_d0 = (ss_d1, RS_stopped (SR_branch BC_EQ (SOff 34 0) (SOff 33 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_d1m : sym_runN src0segs src0tbl FUEL (add_cond ss_d1 C_nxm) = (ss_d1E, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_d2 : sym_runN src0segs src0tbl FUEL ss_d2 = (ss_d2E, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_amc0 : sym_runN src0segs src0tbl FUEL (add_cond ss_amc C_amc0) = (ss_aac, RS_stopped (SR_branch BC_NE (SOff 38 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_r0 : sym_runN src0segs src0tbl FUEL ss_r0 = (ss_rK, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_rF : sym_runN src0segs src0tbl FUEL ss_rF = (ss_rFE, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_rO : sym_run_toN src0segs src0tbl FUEL PC_O ss_rO = (ss_oR, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_aac0 : sym_runN src0segs src0tbl FUEL (add_cond ss_aac C_aac0) = (ss_b0, RS_stopped (SR_branch BC_EQ (SOff 43 0) (SLit 18446744073709551615))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_bd : sym_run_toN src0segs src0tbl FUEL PC_V (add_cond ss_b0 C_bd) = (ss_vBD, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_nbd : sym_runN src0segs src0tbl FUEL (add_cond ss_b0 C_nbd) = (ss_b1, RS_stopped (SR_branch BC_EQ (SOff 43 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_bn : sym_runN src0segs src0tbl FUEL (add_cond ss_b1 C_bn) = (ss_nQ, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_nQ1 : sym_runN src0segs src0tbl FUEL ss_nQ1 = (ss_nG, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_nR : sym_run_toN src0segs src0tbl FUEL PC_V ss_nR = (ss_vBN, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_nGG : sym_runN src0segs src0tbl FUEL ss_nGG = (ss_nK3, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_g1 : sym_runN src0segs src0tbl FUEL (resume_ ss_nK3 (SLit (2 ^ 64 - 12)) (ss_mem ss_nK3)) = (ss_g1, RS_stopped (SR_branch BC_NE (ac_a C_gok1) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_g1' : sym_run_toN src0segs src0tbl FUEL PC_O (add_cond ss_g1 C_gok1) = (ss_oN1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_g2 : sym_runN src0segs src0tbl FUEL (resume_ ss_nK3 (SOff 72 0) (ss_mem ss_nK3)) = (ss_g2, RS_stopped (SR_branch BC_NE (ac_a C_gok2) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_g2' : sym_run_toN src0segs src0tbl FUEL PC_O (add_cond ss_g2 C_gok2) = (ss_oN2, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_bc : sym_runN src0segs src0tbl FUEL (add_cond ss_b1 C_bc) = (ss_cG, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_cR : sym_run_toN src0segs src0tbl FUEL PC_V ss_cR = (ss_vBC, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_cGG : sym_run_toN src0segs src0tbl FUEL PC_O ss_cGG = (ss_oC, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_V : sym_run_toN src0segs src0tbl FUEL (src0_A_alloc_meta + 0x1c4) ss_V = (ss_v1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_v1' : sym_run_toN src0segs src0tbl FUEL (src0_A_alloc_meta + 0x1c8) ss_v1' = (ss_v2, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_v2' : sym_runN src0segs src0tbl FUEL ss_v2' = (ss_vK, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_vF1 : sym_runN src0segs src0tbl FUEL ss_vF1 = (ss_vF1E, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_vG : sym_runN src0segs src0tbl FUEL ss_vG = (ss_vG1, RS_stopped (SR_branch BC_NE (ac_a C_vok) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_vG1 : sym_runN src0segs src0tbl FUEL (add_cond ss_vG1 C_vok) = (ss_vK2, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_vF2 : sym_runN src0segs src0tbl FUEL ss_vF2 = (ss_vF2E, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_vO : sym_run_toN src0segs src0tbl FUEL PC_O ss_vO = (ss_oV, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_O : sym_runN src0segs src0tbl FUEL ss_O = (ss_o1, RS_stopped (SR_branch BC_EQ (SOff 41 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_tl0 : sym_runN src0segs src0tbl FUEL (add_cond ss_o1 C_tl0) = (ss_oE0, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_o2 : sym_runN src0segs src0tbl FUEL ss_o2 = (ss_oE1, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma merge_a2x : mergeb ss_A2 (junk_regs A2_JUNK 57 ss_a2x) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_a2y : forall rs, mergeb ss_A2 (junk_regs A2_JUNK 57 (ss_a2y rs)) = true. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition absO1 (ss : sstate) : sstate := junk_regs [9%bv] 95 ss.
Definition absO2 (ss : sstate) : sstate := junk_regs O_JUNK 96 (absO1 ss).
Definition absO3 (ss : sstate) : sstate := upd_chunk 5 (CTX + 40) (CVal 8 (SOff 108 0)) (absO2 ss).
Definition absO4 (ss : sstate) : sstate := upd_chunk 5 (CTX + 48) (CVal 8 (SOff 109 0)) (absO3 ss).
Definition absO5 (ss : sstate) : sstate := upd_chunk 6 (CTX + 920) (CVal 8 (SOff 110 0)) (absO4 ss).
Lemma merge_oR : mergeb ss_O' (setfacts facts_O (absO5 ss_oR)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_oV : mergeb ss_O' (setfacts facts_O (absO5 ss_oV)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_oN1 : mergeb ss_O' (setfacts facts_O (absO5 ss_oN1)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_oN2 : mergeb ss_O' (setfacts facts_O (absO5 ss_oN2)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_oC : mergeb ss_O' (setfacts facts_O (absO5 ss_oC)) = true. Proof. vm_compute. reflexivity. Qed.
Definition absV1 (ss : sstate) : sstate := junk_regs V_JUNK 74 ss.
Definition absV2 (ss : sstate) : sstate := upd_chunk 6 (CTX + 920) (CVal 8 (SLit (2 ^ 64 - 1))) (absV1 ss).
Lemma merge_vBD : mergeb ss_V (setfacts facts_V (absV2 ss_vBD)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_vBN : mergeb ss_V (setfacts facts_V (absV1 ss_vBN)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma merge_vBC : mergeb ss_V (setfacts facts_V (absV1 ss_vBC)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ss_i1_pc : forall rs, ss_pc (ss_i1 rs) = src0_A_memcpy. Proof. intros [|]; reflexivity. Qed.
Lemma ss_i1_r10 : forall rs, sr_get (ss_regs (ss_i1 rs)) 10%bv = SOff 2 (-64). Proof. intros [|]; reflexivity. Qed.
Lemma ss_i1_r11 : forall rs, sr_get (ss_regs (ss_i1 rs)) 11%bv = SOff 45 8. Proof. intros [|]; reflexivity. Qed.
Lemma ss_i2_eq : forall rs, junk_regs MC_JUNK 46 (ss_i1' rs) = ss_i2 rs. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma ss_rK_pc : ss_pc ss_rK = src0_A_mprotect + 0x30. Proof. reflexivity. Qed.
Lemma ss_vK2_pc : ss_pc ss_vK2 = src0_A_mprotect + 0x30. Proof. reflexivity. Qed.
Lemma ss_vK_pc : ss_pc ss_vK = src0_A_mmap + 0xc4. Proof. reflexivity. Qed.
Lemma ss_nK3_pc : ss_pc ss_nK3 = src0_A_mmap + 0xc4. Proof. reflexivity. Qed.
Lemma ss_nQ_pc : ss_pc ss_nQ = src0_A_alloc_meta + 0x144. Proof. reflexivity. Qed.
Lemma ss_nG_pc : ss_pc ss_nG = src0_A_alloc_meta + 0x168. Proof. reflexivity. Qed.
Lemma ss_cG_pc : ss_pc ss_cG = src0_A_alloc_meta + 0x12c. Proof. reflexivity. Qed.
Lemma finals_pc : map ss_pc [ss_cE; ss_d1E; ss_d2E; ss_rFE; ss_vF1E; ss_vF2E; ss_oE0; ss_oE1] = repeat PC_RET 8.
Proof. vm_compute. reflexivity. Qed.
End a.
