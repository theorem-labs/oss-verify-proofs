(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 223 of its 252 lines of code are new or changed and 1051 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm (preset_file.c:454-476, A_put 0x8449c, 612 bytes), the case
   `failed = 0 /\ cap < len + n + 1`, where put must enlarge the buffer before it copies. The image-B twin of
   lib/A/FSW_put_grow.v.

   The arm is: the need test at 0x8454c (its BC_LTU side), the `cap <> 0` test at 0x84554, the doubling loop whose
   head is the `bltu s6, a0` at 0x84564, and the call of the PROGRAM function fuzz_realloc 0x82bc4 with ra = 0x84580;
   after the call the granted side re-joins the fast arm's code at 0x845a0 (UBSan's checks of buf + len, the
   __asan_memcpy of bs, the length store, the terminating 0) with the new buffer. This file carries the loop:
   everything from the loop head to the call site.

   B IS NOT A's CODE: s3 / s4 are swapped (B: s3 = o >> 3, s4 = o + 24), the need sits in a0 (A: a2), and o + 8 is
   s6 until 0x84550 spills it to sp - 112 (A: a0). MEASURED with the token engine on B (lane scratch probe, a build
   machine, 2026-10-29T09:2xZ; Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan,
   SH := FSW_put.fsw_pf_SH = [mkSHE 10 0 32]); every run sh_chk = true, sh_obls = [], sh_j = 0:
   - from the entry state with this file's atom facts fsw_pg_gf (run_K 36): run 1 stops at 542028 = 0x8454c,
     SR_branch BC_GEU (SOff 35 0) (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)); its BC_LTU side stops at 542036 = 0x84554,
     SR_branch BC_NE (SOff 35 0) (SLit 0) (UBSan's alignment check of o at 0x844dc is passed on the way, by atom 10's
     af_al2 = 3);
   - cap = 0: stops at the head 542052 = 0x84564 with reg 22 = SLit 4096, reg 11 = SLit 8192; cap <> 0: stops at the
     head with reg 22 = SLL cap 1, reg 11 = SLL cap 2 (the engine decides the first `cap <u need` from the path
     condition); every other register is fsw_pg_regs', and ss_mem is fsw_pg_mem on both sides;
   - from fsw_pg_ssl (run_K 37, sh_static_ok true): the stop at 542052 is SR_branch BC_LTU (SOff 36 0) need; its taken
     side returns to 542052 with regs fsw_pg_regs2, the same ss_mem and the same atom facts; its BC_GEU side stops at
     the FETCH of 535492 = A_fuzz_realloc (fsw_pg_ssc below).

   TAKEN FROM: lib/A/FSW_put_grow.v at a working branch 860b2fb1188 (the same blob is on
   a working branch f0e2574c33c): the state definitions with B's registers and pcs, fsw_pg_sll1 / 2,
   fsw_pg_backedge, pg_run_mem and fsw_pg_loop unchanged in form (B's table fsw_put_tbl for A's fsw_wr_tbl).

   Kit used by path, never copied: lib/B/FSW_K.v, lib/B/FSW_put.v (fsw_put_tbl, fsw_pf_SH, fsw_pf_o_region,
   fsw_pf_CEIL), lib/A/FSupoisonStack.v.

   RULE-24: proves function put (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x8449c; the GROW arm)
   (reuse search: proof-index put_holds / put_close_grow / fsw_pg_loop / pgt_run / fsw_pg_entry_run, index v5
   built 2026-10-29T07:26:27Z, plus a git grep with a passing control (put_failed_run) of 599 cold lib/B trees: no
   lib/B/FSW_put_grow* or FSW_put_holds* anywhere; checker a Theorem Labs lane CONFIRM 09:2xZ). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_ret FSW_put.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the loop-head state at 0x84564 (MEASURED on B, see the header). Atom 36 is the loop's candidate capacity c: it is a
   FRESH atom, so the loop lemma can re-abstract it to 2 * c at the back edge (ewset E 36; atoms below 36 are
   untouched, ew_ewset_other). Its afact is mkAF 4096 (2 ^ 27) 0: the first candidate is 4096 (cap = 0) or
   2 * cap (cap <> 0, and a live buffer is at least 4096 by the allocator's class), and the loop exits at the
   first candidate at or above need <= WMAX = 2 ^ 27. ---- *)
Definition fsw_pg_regs (c : sv) : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-112); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 10 0; SOff 12 0;
   SAlu ALU_ADD (SOff 12 1) (SOff 34 0); SAlu ALU_SLL c (SLit 1); SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 11 0; SAlu ALU_SRL (SOff 10 0) (SLit 3); SOff 10 24; SOff 10 16; c; SOff 32 0;
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0);
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0);
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0);
   SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* atom 33 = buf: at cap = 0 wout_ok gives buf = 0, so the fast arm's fact 4096 <= buf (fsw_pf_gf) is false on the
   cap = 0 side; the loop never reads through buf, so its fact is relaxed to 0 <= buf here (found by a Theorem Labs lane) *)
Definition fsw_pg_gf : list (nat * afact) :=
  [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (33%nat, mkAF 0 fsw_pf_CEIL 4); (34%nat, mkAF 0 (2 ^ 27) 0);
   (35%nat, mkAF 0 (2 ^ 27) 0); (12%nat, mkAF 0 (2 ^ 27) 0)].
Definition fsw_pg_facts : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ::
           (36%nat, mkAF 4096 (2 ^ 27) 0) :: fsw_pg_gf) [] [].
(* put's frame at the loop head, as the entry path leaves it (MEASURED on B on both sides of the `cap <> 0` test):
   the fourteen words - o + 8 (s6) spilled at sp - 112 by 0x84550, then s11 .. s2, s1, s0 and ra - kept as chunks, so that the engine carries them through the loop to the call and the resume after fuzz_realloc can read
   the saved registers back (A's Theorem Labs lane found that a chunk-free frame loses them) *)
Definition fsw_pg_cs : list YP09.chunk :=
  [YP09.mkChunk (-112) (CVal 8 (SOff 10 8)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition fsw_pg_mem : list YP09.region :=
  [YP09.mkRegion (Some 2%nat) (- FRAME_put) 0 (- FRAME_put) 0 fsw_pg_cs; fs_got_region; fs_bcell_region 32;
   fsw_pf_o_region].
Definition fsw_pg_ssl : sstate := mkSS 542052 (fsw_pg_regs (SOff 36 0)) fsw_pg_mem None fsw_pg_facts.

(* The two numbers the loop lemma's run step needs, checked here: the token engine's static shadow check passes on
   the loop-head state, and its run ceiling is 37 (MEASURED on B, the same as A's). *)
Example fsw_pg_K : run_K 0 fs_Bx fsw_pf_SH fsw_pg_ssl = 37%nat.
Proof. vm_compute. reflexivity. Qed.
Example fsw_pg_static :
  sh_static_ok (run_K 0 fs_Bx fsw_pf_SH fsw_pg_ssl) fs_Bx fs_Bspan fsw_pf_SH (ss_facts fsw_pg_ssl) (ss_mem fsw_pg_ssl) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================= the doubling loop at 0x84564 ================= *)
(* The head 0x84564 `bltu s6, a0` tests `c <u need`, need = n + 1 + len (reg 10 = a0 at the head in B, atom 12 = n
   and atom 34 = len). The taken side runs one body (0x8455c `mv s6, a1`, 0x84560 `slli a1, a1, 1`) and comes BACK
   to 0x84564 with reg 22 = SLL c 1 and reg 11 = SLL c 2 - NOT the syntactic
   fold SLL (SLL c 1) 1 - so the candidate is RE-ABSTRACTED at the back edge (ewset E 36; atoms below 36 are
   untouched, YP03.ew_ewset_other), which is what fsw_pg_backedge does. The exit side runs to the FETCH stop at
   the program function fuzz_realloc 0x82bc4 with ra = 0x84580 (MEASURED on B: SR_fetch at 535492, sh_obls = [];
   on the way it passes the inline check of o's shadow at 0x8456c / 0x84570, report site 0x846ec, by the shadow
   entry fsw_pf_SH of o's 32 bytes).
   TEMPLATE (never a copied term), cited per the lane rule: the bespoke ASan line's put_blocks.v put_loop
   (a Theorem Labs lane's put_blocks.v:356-377) is the same
   fuel induction with the same invariant `need <= v * 2 ^ f` and the same `dbl f v need` result; its engine
   (Exec.evt over a register record, no journal, no ARU, no token shadow state) is not this one, so nothing of
   it is reusable as a term. dbl_pow / newcap_pow (:324-351) are the class facts, re-proved on our side in
   lib/A/FSW_put_grow_model.v (B twin: lib/B/FSW_put_grow_model.v). *)
Definition fsw_pg_need : sv := SAlu ALU_ADD (SOff 12 1) (SOff 34 0).
Definition fsw_pg_regs2 : list sv :=
  sr_set (fsw_pg_regs (SAlu ALU_SLL (SOff 36 0) (SLit 1))) 11%bv (SAlu ALU_SLL (SOff 36 0) (SLit 2)).
(* the state at the call (MEASURED on B): ra = 0x84580, a0 = buf, a1 = s6 = c, s0 = o, s1 = n, s2 = s,
   s11 = the shadow address of o, sp = entry sp - 112; ss_mem is the head's *)
Definition fsw_pg_ssc : sstate := Eval vm_compute in
  sh_ss (fst (sym_runN_tok tfibsegs fsw_put_tbl 37%nat fs_Bx fs_Bspan fsw_pf_SH FUEL
                (add_cond fsw_pg_ssl (mkAC BC_GEU (SOff 36 0) fsw_pg_need)))).
Example fsw_pg_ssc_pc : ss_pc fsw_pg_ssc = A_fuzz_realloc.
Proof. vm_compute. reflexivity. Qed.
Example fsw_pg_ssc_ra : sr_get (ss_regs fsw_pg_ssc) 1%bv = SLit 542080.
Proof. vm_compute. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the two shifts the body leaves behind ---- *)
Lemma fsw_pg_sll1 : forall (E : env) c, ew E 36%nat = Z_to_bv 64 c -> 0 <= c -> 2 * c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLL (SOff 36%nat 0) (SLit 1)) = Z_to_bv 64 (2 * c).
Proof.
intros E c H Hc H64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E 36%nat c H ltac:(lia)).
replace (YP0e.U E (SLit 1)) with 1 by (vm_compute; reflexivity).
cbn [zalu_raw]. change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 1) with 2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma fsw_pg_sll2 : forall (E : env) c, ew E 36%nat = Z_to_bv 64 c -> 0 <= c -> 4 * c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLL (SOff 36%nat 0) (SLit 2)) = Z_to_bv 64 (4 * c).
Proof.
intros E c H Hc H64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E 36%nat c H ltac:(lia)).
replace (YP0e.U E (SLit 2)) with 2 by (vm_compute; reflexivity).
cbn [zalu_raw]. change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the back edge: the state at 0x84564 one body later IS the loop head again, at the atom re-abstracted
   to 2 * c. Every atom the state reads but 36 is untouched by the ewset. ---- *)
Lemma fsw_pg_backedge : forall (W : world tfibsegs) (E : env) ms (ss : sstate) (c : Z),
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ss_pc ss = 542052 -> ss_regs ss = fsw_pg_regs2 -> ss_resv ss = None ->
  ss_mem ss = ss_mem fsw_pg_ssl -> f_atoms (ss_facts ss) = f_atoms fsw_pg_facts ->
  ew E 36%nat = Z_to_bv 64 c -> 4096 <= c -> 2 * c <= 2 ^ 27 ->
  st_ok tfibsegs (ewset E 36%nat (Z_to_bv 64 (2 * c))) fsw_pg_ssl (restrict (w_H W) ms).
Proof.
intros W E ms ss c HS Hpc Hregs Hresv Hmem Hat E36 Hc1 Hc2.
change (2 ^ 27) with 134217728 in Hc2.
assert (HA : env_agree 36%nat E (ewset E 36%nat (Z_to_bv 64 (2 * c)))) by apply env_agree_ewset.
assert (Hc0 : 0 <= c) by lia.
assert (H64 : 0 <= 4 * c < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
(* everything the proof needs from the state after the body, read off once *)
pose proof (st_ok_regs_ok tfibsegs E ss _ HS) as HR. unfold regs_ok in HR. cbn [ms_regs restrict] in HR.
rewrite Hregs in HR.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as HM. cbn [ms_mem restrict] in HM. rewrite Hmem in HM.
assert (HM' : mem_ok tfibsegs (ewset E 36%nat (Z_to_bv 64 (2 * c))) (mrestrict (w_H W) (ms_mem ms))
                (ss_mem fsw_pg_ssl)).
{ apply (mem_ok_agree tfibsegs 36%nat E); [exact HA | vm_compute; reflexivity | exact HM]. }
pose proof (st_ok_facts_ok tfibsegs E ss _ HS) as HF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hresv) as Ems. rewrite Hpc in Ems.
clear HS HM.
set (E' := ewset E 36%nat (Z_to_bv 64 (2 * c))) in *.
assert (E36' : ew E' 36%nat = Z_to_bv 64 (2 * c)) by (unfold E'; apply ew_ewset_same).
(* the machine's shape at the loop head *)
rewrite Ems, restrict_mkst_fx.
destruct HM' as (Hwf & Hrok & Hpd).
apply (entry_st_ok_any tfibsegs E' 542052 (fsw_pg_regs (SOff 36 0)) (ms_regs ms) fsw_pg_mem fsw_pg_facts
         (mrestrict (w_H W) (ms_mem ms))); [ | exact Hwf | exact Hrok | exact Hpd | ].
- (* the registers: 22 and 11 carry the candidate, every other one reads atoms below 36 only *)
  assert (V22 : sv_denot E (SAlu ALU_SLL (SOff 36%nat 0) (SLit 1)) = Z_to_bv 64 (2 * c))
    by (apply fsw_pg_sll1; [exact E36 | lia | lia]).
  assert (V11 : sv_denot E (SAlu ALU_SLL (SOff 36%nat 0) (SLit 2)) = Z_to_bv 64 (4 * c))
    by (apply fsw_pg_sll2; [exact E36 | lia | lia]).
  assert (W22 : sv_denot E' (SOff 36%nat 0) = Z_to_bv 64 (2 * c)) by (rewrite fsw_SOff0; exact E36').
  assert (W11 : sv_denot E' (SAlu ALU_SLL (SOff 36%nat 0) (SLit 1)) = Z_to_bv 64 (4 * c)).
  { rewrite (fsw_pg_sll1 E' (2 * c) E36' ltac:(lia) ltac:(lia)). f_equal. lia. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
    rewrite HR;
    lazymatch goal with
    | |- sv_denot ?Ea (sr_get ?sa ?ra) = sv_denot ?Eb (sr_get ?sb ?rb) =>
        let va := eval vm_compute in (sr_get sa ra) in change (sr_get sa ra) with va;
        let vb := eval vm_compute in (sr_get sb rb) in change (sr_get sb rb) with vb
    end;
    first
    [ rewrite V22, W22; reflexivity
    | rewrite V11, W11; reflexivity
    | symmetry; apply (sv_denot_agree 36%nat E E'); [exact HA | vm_compute; reflexivity] ].
- (* the facts: every atom but 36 is untouched; atom 36 is the new candidate *)
  destruct HF as (HFa & _ & _). rewrite Hat in HFa.
  unfold facts_ok. split; [|split; [exact I | exact I]].
  unfold fsw_pg_facts, fsw_pg_gf in HFa |- *. cbn [f_atoms atoms_ok] in HFa |- *.
  destruct HFa as (A2 & A32 & _ & A10 & A33 & A34 & A35 & A12 & _).
  assert (OTH : forall n f, n <> 36%nat -> afact_ok E n f -> afact_ok E' n f).
  { intros n f Hn Hf. unfold afact_ok in *. unfold E'. rewrite (ew_ewset_other E 36%nat _ n Hn). exact Hf. }
  split; [apply OTH; [discriminate | exact A2]|].
  split; [apply OTH; [discriminate | exact A32]|].
  split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E36', (wz (2 * c) ltac:(lia)).
    split; [change (2 ^ 27) with 134217728; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
  split; [apply OTH; [discriminate | exact A10]|].
  split; [apply OTH; [discriminate | exact A33]|].
  split; [apply OTH; [discriminate | exact A34]|].
  split; [apply OTH; [discriminate | exact A35]|].
  split; [apply OTH; [discriminate | exact A12] | exact I].
Qed.

(* one run from a state whose only writable region is put's frame at atom 2 (bv_unsigned (ew E 2) = sp, E2sp)
   writes nothing outside [sp - FRAME_put, sp) and keeps every present byte (put_fast_run's run-1 step, FSW_put.v) *)
Ltac pg_run_mem ms sp E2sp :=
  lazymatch goal with
  | HF : frame_of _ _ (ms_mem ms) (ms_mem ?mB), HG : mem_grows _ _ |- _ =>
    let M1 := fresh "M1" in let PR1 := fresh "PR1" in
    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - FRAME_put <= a < sp) ->
                   ms_mem mB (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a));
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
      let r := fresh "r" in let Hri := fresh "Hri" in let Hr := fresh "Hr" in
      intros a Ha Hna; apply HF; rewrite (wz a Ha); intros (r & Hri & Hr);
      vm_compute in Hri; repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2sp in Hr; unfold FRAME_put in Hna; lia
    | pose proof (fun a => apresent_grows _ _ _ a HG) as PR1 ]
  end.

(* ---- the loop: a fuel induction (at most 16 doublings, since 4096 <= c and need <= WMAX = 2 ^ 27), the invariant
   `need <= c * 2 ^ kf` (the template's, put_blocks.v:357). The continuation is ABSTRACT: it receives the call-site
   state fsw_pg_ssc with atom 36 = dbl kf c need, the journal and ARU at the call, the env's agreement below 36
   with the head's (every atom the rest of the walk reads is below 36), and the two memory facts the second half
   needs: the loop wrote nothing outside put's frame [sp - FRAME_put, sp), and it kept every present byte ---- *)
Lemma fsw_pg_loop :
  forall (kf : nat) (W : world tfibsegs) (Q : world tfibsegs -> config -> Prop)
         STK sp0 FP ly S W0 mem0 md own lyc Sc U k
         (E : env) (ms : machine_state) (mdc : Model) (c need sp : Z),
  st_ok tfibsegs E fsw_pg_ssl (restrict (w_H W) ms) ->
  sh_ok tfibsegs fs_Bx fsw_pf_SH E (mrestrict (w_H W) (ms_mem ms)) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  (forall E2, env_agree 36%nat E E2 ->
     awr_ok tfibsegs B E2 (ss_mem fsw_pg_ssl) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S)) ->
  bv_unsigned (ew E 2%nat) = sp ->
  ew E 36%nat = Z_to_bv 64 c -> YP0e.U E fsw_pg_need = need ->
  4096 <= c -> c <= WMAX -> (exists j, 0 <= j /\ c = 4096 * 2 ^ j) -> 0 <= need <= WMAX ->
  need <= c * 2 ^ Z.of_nat kf ->
  (forall (E' : env) (ms' : machine_state) (mdc' : Model),
     env_agree 36%nat E E' ->
     ew E' 36%nat = Z_to_bv 64 (WriterSpec.dbl kf c need) ->
     st_ok tfibsegs E' fsw_pg_ssc (restrict (w_H W) ms') ->
     sh_ok tfibsegs fs_Bx fsw_pf_SH E' (mrestrict (w_H W) (ms_mem ms')) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - FRAME_put <= a < sp) ->
        ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
     (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros kf. induction kf as [|kf IH];
  intros W Q STK sp0 FP ly S W0 mem0 md own lyc Sc U k E ms mdc c need sp
    HS SHOK HJ HARU HAWR E2sp E36 HU Hc1 HcW Hcls Hn Hfuel K;
  unfold WMAX in HcW, Hn; unfold fsw_pg_need in HU;
  assert (Uc : YP0e.U E (SOff 36%nat 0) = c) by (apply (U_atom E 36%nat c E36); lia).
- (* fuel 0: need <= c, so the test falls through to the call *)
  assert (Hge : need <= c) by (cbn [Z.of_nat] in Hfuel; rewrite Z.pow_0_r in Hfuel; lia).
  srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
  + exfalso. rewrite branch_ltu_U, Uc, HU in Hc. apply Z.ltb_lt in Hc. lia.
  + fsw_aj_run_tokU fsw_put_tbl_ok HS HJ HARU SHOK fs_Bspan.
    * exact (HAWR E (env_agree_refl 36%nat E)).
    * pg_run_mem ms sp E2sp.
      eapply K; [apply env_agree_refl | cbn [WriterSpec.dbl]; exact E36 | exact HS | exact SHOK | exact HJ | exact HARU
                | exact M1 | exact PR1].
- srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
  + (* taken: c < need - one body, the back edge, and the loop again at 2 * c *)
    assert (Hlt : c < need) by (rewrite branch_ltu_U, Uc, HU in Hc; apply Z.ltb_lt in Hc; exact Hc).
    destruct Hcls as (j & Hj & Hcj).
    assert (Hj14 : j <= 14).
    { destruct (Z_le_gt_dec j 14) as [Hle|Hgt]; [exact Hle|]. exfalso.
      assert (P : 2 ^ 15 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 15) with 32768 in P. change (2 ^ 27) with 134217728 in Hn. lia. }
    assert (H2c : 2 * c <= 2 ^ 27).
    { assert (P : 2 ^ j <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 14) with 16384 in P. change (2 ^ 27) with 134217728. lia. }
    fsw_aj_run_tokU fsw_put_tbl_ok HS HJ HARU SHOK fs_Bspan.
    * exact (HAWR E (env_agree_refl 36%nat E)).
    * pg_run_mem ms sp E2sp.
      pose proof (fsw_pg_backedge W E _ _ c HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        E36 Hc1 H2c) as HS2.
      assert (HA2 : env_agree 36%nat E (ewset E 36%nat (Z_to_bv 64 (2 * c)))) by apply env_agree_ewset.
      eapply (IH W Q STK sp0 FP ly S W0 mem0 md own lyc Sc U k (ewset E 36%nat (Z_to_bv 64 (2 * c))) _ _
                (2 * c) need sp HS2).
      -- eapply (sh_ok_agree tfibsegs fs_Bx fsw_pf_SH 36%nat E); [exact HA2 | vm_compute; reflexivity | exact SHOK].
      -- exact HJ.
      -- exact HARU.
      -- intros E3 HA3. apply HAWR. eapply env_agree_trans; [exact HA2 | exact HA3].
      -- rewrite (ew_ewset_other E 36%nat _ 2%nat ltac:(lia)). exact E2sp.
      -- apply ew_ewset_same.
      -- (* need reads atoms 12 and 34 only: the ewset at 36 leaves it, by computation *)
         rewrite <- HU. reflexivity.
      -- lia.
      -- unfold WMAX. exact H2c.
      -- exists (j + 1). split; [lia|]. rewrite Z.pow_add_r by lia. rewrite Hcj. change (2 ^ 1) with 2. ring.
      -- unfold WMAX. exact Hn.
      -- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
         replace (2 * c * 2 ^ Z.of_nat kf) with (c * (2 * 2 ^ Z.of_nat kf)) by ring. exact Hfuel.
      -- intros E' ms' mdc' HA' Hew HS' SHOK' HJ' HARU' M1' PR1'.
         apply (K E' ms' mdc'); [eapply env_agree_trans; [exact HA2 | exact HA'] | | exact HS' | exact SHOK'
                                | exact HJ' | exact HARU' | | ].
         ++ rewrite Hew. f_equal. cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_gt need c) Hlt). reflexivity.
         ++ intros a Ha Hna. rewrite (M1' a Ha Hna). exact (M1 a Ha Hna).
         ++ intros a Ha. exact (PR1' a (PR1 a Ha)).
  + (* not taken: need <= c - the exit to the call *)
    assert (Hge : need <= c) by (rewrite branch_ltu_U, Uc, HU in Hc; apply Z.ltb_ge in Hc; exact Hc).
    fsw_aj_run_tokU fsw_put_tbl_ok HS HJ HARU SHOK fs_Bspan.
    * exact (HAWR E (env_agree_refl 36%nat E)).
    * pg_run_mem ms sp E2sp.
      eapply K; [apply env_agree_refl | | exact HS | exact SHOK | exact HJ | exact HARU | exact M1 | exact PR1].
      cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_le need c) Hge). exact E36.
Qed.

End w.
