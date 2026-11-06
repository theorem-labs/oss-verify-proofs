(* fs program part, READER group, image B (fs.asan-ubsan): the ASan walk of parse_string (A_parse_string 0x85534,
   pf.c:117-181), PLAIN-BYTE CASE: stage 1 and the two halves of the fuzz_malloc call step that need no In-CTX premise.
   Stage 2 is lib/B/FSW_parse_string_s2.v.
   rule 24: proves function parse_string, image B (reuse search: proof-index parse_string, unpiped,
   2026-10-29T04:09Z, index v5 built 04:08:23Z, 169 lines, last line `proof-index: end; parse_string: 14 named,
   128 by address, 4 related, 17 lemma(s), [the delivered package] 56 named and 725 name(s) holding it` = a Theorem Labs lane's
   idx-B-parse_string.txt; by ADDRESS: image B entry 0x85534, no trampoline / REAL slot (a Theorem Labs lane's
   reuse-parse_string.md:13-18); named cold branches: lib/B files naming parse_string are only the statement
   files FSH_Fn_reader.v / FSH_Fn_writer.v; the only lib/B proofs are a working branch 955803f9b2e
   lib/B/Prog/parse_string.v, stated over another engine, so a template, not a port source. CONFIRM (2026-10-29T04:34Z,
   a Theorem Labs lane): "CONFIRM: reuse search for parse_string (B) holds").

   TEMPLATES. (1) image A's walk over the same S0 statement form, PROVED: a working branch 9f3343583b7
   lib/A/FSW_parse_string.v (Section W :108-1047 stage 1, pstr_scan_loop :464, pstr_stage1 :731; Section W3
   :2006-2251 the call step pstr_call_step :2091, split here at its step 3 into pstr_call_pre / pstr_call_post).
   Its structure, definitions and lemma names are ported; the addresses, the register allocation and the cut points
   are B's. (2) the bespoke B proof,
   a working branch 955803f9b2e lib/B/Prog/parse_string.v :1027 (aps_loop_evt, the scan loop) and
   lib/B/Prog/parse_string_segs.v :39-47 (aps_out, B's registers): B's cut points and register facts; not imported.
   The shared definitions (pstr_call_facts, pstr_ret_facts, the shadow lemmas) are lib/B/FSW_parse_string_defs.v.

   THE SHAPE (as image A's). parse_string runs at FP = FS_PSTAT_FP and calls fuzz_malloc, which also runs at
   FP = FS_PSTAT_FP; the journals compose over the FP-keyed core.
     stage 1  pstr_stage1      entry 0x85534 -> the fuzz_malloc call 0x85614 (the escape-free scan loop), in
                               continuation form: it consumes a continuation at the callee's entry A_fuzz_malloc
                               under pstr_call_facts and gives SRr at the entry.
     call     (pending)        the call: pstr_call_pre (the callee's fpreU by FSW_ret.v fsw_fpreU_atFP and
                               fuzz_malloc_spec's other premises at n = Q + 1), fuzz_malloc_spec itself, and
                               pstr_call_post (from its post, the journal composition FSW_K3.v fsw_rt_atU3, its FP
                               arm: the four statics are image bytes, pc_fp_img), giving pstr_ret_facts at the return
                               0x85618.
     stage 2  pstr_stage2      (lib/B/FSW_parse_string_s2.v) the return 0x85618 -> the `ret` 0x85a5c.
   THE COMPOSITION parse_string_proof : forall CTX, parse_string_spec CTX waits for the owner-approved spec change
   (a Theorem Labs lane 2026-10-29 05:00Z): fuzz_malloc_spec's premise `In (raZ regs :: spine ch) CTX` is dropped (A and B).
   The current lib/B/FSH_Fn_alloc.v fuzz_malloc_spec still takes it, and parse_string_spec gives nothing for the call's
   chain (its s0 is the data pointer q), so the call step and the composition follow when the new spec lands; no
   interim (_c5) statement is made for B.

   THE CODE (a Theorem Labs lane's parse_string.B.s, 386 four-byte instructions 0x85534 .. 0x85b3c; the cut words checked
   by lib/B/FSW_parse_string_tbl.v parse_string_tbl_probe): prologue 0x85534 .. 0x85568; `mv s0,a0` 0x8556c; the
   alignment check `andi a0,a0,7; bnez a0` 0x85570 (to the UBSan trap 0x85a90; the engine decides it from q's
   8-alignment fact); the shadow base through the GOT 0x85578 `auipc a0,0x1a` + 0x8557c `ld a0,0x698(a0)` (the GOT
   word 0x9fc10) + 0x85580 `ld s7,0(a0)`; the shadow check of in->p 0x85584 .. 0x85590 (s6); the first stop is the
   load of in->p 0x85594, where the walk reseats with struct pj_in as one region at s0; then in->p + 1 < 2 (0x855a0,
   decided from the text's range fact), the shadow check of in->end 0x855a8 .. 0x855b4 (s8), the exit test
   `bgeu s4,a1` 0x855bc (refuted), the scan loop 0x855c8 .. 0x855f8 (per byte: the 1-byte shadow check of the cursor,
   the quote test 0x855dc, the cursor-overflow trap test 0x855f0 (refuted), the back branch 0x855f8), and at the quote
   0x8560c `sub a0,a0,s4; addi a0,a0,1; jal fuzz_malloc` 0x85614 (return 0x85618). No __asan_report_* branch is
   taken. No Admitted, no Axiom, no Parameter, no admit, no timeout. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_K3 FSW_parse_string_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_parse_string_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_parse_string_s2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
Import ListNotations.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair the kit's entry states need (lib/B/FSH_Base.v FsShadowSyms: the GOT word 0x9fc10 and the
   cell 0xa8438 of __asan_shadow_memory_dynamic_address, = B/YB1w.v's tfib_D_* names) *)
Hypothesis HSS : FsShadowSyms B.
Let TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

(* ---- arithmetic of the scan loop (pf.c:123: the cursor advances by 2 at a backslash, else by 1; B computes the
   step as `seqz (c - 0x5c) + 1` 0x855e0 .. 0x855e8 and adds it 0x855f4): for a byte that is not a backslash the step
   is 1 ---- *)
Lemma pstr_sltu_nz : forall E (v : sv), U E v <> 0 -> U E (SAlu ALU_SLTU v (SLit 1)) = 0.
Proof.
intros E v Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
pose proof (U_range E v) as Hr.
replace (U E v <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma pstr_off_nz : forall E n c k, ew E n = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 -> - 2 ^ 63 < k < 2 ^ 63 ->
  c + k <> 0 -> c + k <> 2 ^ 64 -> U E (SOff n k) <> 0.
Proof.
intros E n c k Hn Hc Hk Hz Hz2. rewrite U_SOff, Hn, (unsigned_lit_small c) by lia.
unfold zcanon, M64. intros Hm. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [z Hzz].
assert (Hb : - 2 ^ 63 < c + k < 2 ^ 64 + 2 ^ 63) by lia. nia.
Qed.
(* the scan loop's seqz is 0 on a byte that is not a backslash *)
Lemma pstr_sltu_not92 : forall E c, 0 <= c < 256 -> c <> 92 -> ew E 32 = Z_to_bv 64 c ->
  U E (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) = 0.
Proof.
intros E c Hc Hne H32. apply pstr_sltu_nz.
apply (pstr_off_nz E 32 c (-92) H32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
(* the step a3 = seqz (c - 0x5c) + 1 (0x855e8) is 1 *)
Lemma pstr_step_val : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 -> c <> 92 ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1)) = 1.
Proof.
intros E c H32 Hc Hne.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (pstr_sltu_not92 E c Hc Hne H32), U_SLit, (zcanon_id 1) by (unfold M64; lia).
rewrite Z.add_0_l. apply zcanon_id. unfold M64. lia.
Qed.

(* ---- the two values the loop body computes: the cursor after a plain byte (0x855f4 `add a0,a0,a3`), and the length
   a0 = Q + 1 at the fuzz_malloc call (0x8560c `sub a0,a0,s4` + 0x85610 `addi a0,a0,1`) ---- *)
Lemma pstr_loop_cond_val : forall E c x, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 -> c <> 92 ->
  ew E 10 = Z_to_bv 64 x -> 0 <= x -> x + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1))) = x + 1.
Proof.
intros E c x H32 Hc Hne H10 Hx0 Hx1.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (pstr_step_val E c H32 Hc Hne), (U_atom E 10 x H10 ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma pstr_len_val : forall E x s, ew E 10 = Z_to_bv 64 x -> ew E 20 = Z_to_bv 64 s ->
  0 <= x -> x + 1 < 2 ^ 64 -> 0 <= s <= x + 1 ->
  U E (SAlu ALU_ADD (SOff 10 1) (SMd M_MUL (SOff 20 0) (SLit (2 ^ 64 - 1)))) = x + 1 - s.
Proof.
intros E x s H10 H20 Hx0 Hx1 Hs.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom_off E 10 x 1 H10 ltac:(lia) ltac:(lia)), (U_atom E 20 s H20 ltac:(lia)), U_SLit.
rewrite (zcanon_id (2 ^ 64 - 1)) by (unfold M64; lia).
unfold zcanon, M64.
rewrite Zplus_mod_idemp_r.
replace (x + 1 + s * (2 ^ 64 - 1)) with ((x + 1 - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ---- the scan loop's head state (0x855c8): every register an atom, a2 pinned to the quote literal, the text byte
   at the cursor a0 as a 1-byte region with the byte as atom 32, and the shadow base in s7 (atom 23) as the token
   run's Bx ---- *)
Definition pstr_BxL : sv := SOff 23 0.
Definition pstr_regsL : list sv := sr_set sr_atoms 12%bv (SLit 34).
Definition pstr_regionL : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition pstr_factsL : facts := mkFacts
  [(10%nat, mkAF RTLO RTHI 0); (11%nat, mkAF RTLO RTHI 0); (20%nat, mkAF RTLO RTHI 0);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 32 255 0)] [] [].
Definition pstr_ssL : sstate := mkSS PSTR_SCAN pstr_regsL [pstr_regionL] None pstr_factsL.

Lemma pstr_ssL_ok : forall (W : world tfibsegs) regs1 mem1 x c tl pp1,
  YK11.getr regs1 10 = w64 x -> YK11.getr regs1 11 = w64 tl -> YK11.getr regs1 12 = w64 34 ->
  YK11.getr regs1 20 = w64 pp1 -> YK11.getr regs1 23 = w64 SHADOW_OFF ->
  RTLO <= x <= RTHI -> RTLO <= tl <= RTHI -> RTLO <= pp1 <= RTHI ->
  32 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) x 1 c ->
  st_ok tfibsegs (Ereg regs1 [w64 c]) pstr_ssL
    (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 PSTR_SCAN) mem1 (YK11.seg_rom tfibsegs))).
Proof.
intros W regs1 mem1 x c tl pp1 H10 H11 H12 H20 H23 Hx Htl Hpp Hc Hval.
assert (E10 : bv_unsigned (ew (Ereg regs1 [w64 c]) 10) = x)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl), H10; apply wz; unfold RTLO, RTHI in *; lia).
assert (E11 : bv_unsigned (ew (Ereg regs1 [w64 c]) 11) = tl)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 11 11%bv eq_refl), H11; apply wz; unfold RTLO, RTHI in *; lia).
assert (E20 : bv_unsigned (ew (Ereg regs1 [w64 c]) 20) = pp1)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 20 20%bv eq_refl), H20; apply wz; unfold RTLO, RTHI in *; lia).
assert (E23 : bv_unsigned (ew (Ereg regs1 [w64 c]) 23) = SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 23 23%bv eq_refl), H23; apply wz; unfold SHADOW_OFF; lia).
assert (E32 : ew (Ereg regs1 [w64 c]) 32 = Z_to_bv 64 c)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs1 [w64 c]) 32) = c) by (rewrite E32; apply wz; lia).
rewrite restrict_mkst_fx. unfold pstr_ssL. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros Hq; discriminate Hq |].
  rewrite H12. cbn [sv_denot]. apply bv_eq. rewrite unsigned_lit_small by lia. unfold w64. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold pstr_regionL, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10. split; [unfold RTLO in *; lia|]. split; [unfold RTHI in *; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ x 0 1 (SOff 32 0) c);
    [rewrite fsw_SOff0, E32; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Hval].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. unfold pstr_factsL. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2].
  rewrite E10, E11, E20, E23, U32.
  rewrite !Z.pow_0_r.
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [unfold SHADOW_OFF; lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I].
Qed.

Lemma pstr_byte_eq_dec : forall (E : env) c b, ew E 32 = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SLit 34)) = b -> (c =? 34) = b.
Proof.
intros E c b H32 Hb Hc. rewrite branch_eq_U, (U_atom E 32 c H32 Hb), (U_lit E 34 ltac:(lia)) in Hc. exact Hc.
Qed.

(* ---- the loop-head machine state of the escape-free scan (0x855c8), at the cursor x ---- *)
Definition pstr_loop_at (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ot q p text len x : Z)
  (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  YK11.getr regs1 10 = w64 x /\ YK11.getr regs1 11 = w64 (text + len) /\ YK11.getr regs1 12 = w64 34 /\
  YK11.getr regs1 20 = w64 (p + 1) /\
  YK11.getr regs1 8 = w64 q /\ YK11.getr regs1 9 = w64 (q + 8) /\
  YK11.getr regs1 22 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regs1 23 = w64 SHADOW_OFF /\
  YK11.getr regs1 24 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  YK11.getr regs1 3 = YK11.getr regs 3 /\ YK11.getr regs1 4 = YK11.getr regs 4 /\
  spZ regs1 = spZ regs - FRAME_PSTR /\
  (forall y : word, ~ (spZ regs - FRAME_PSTR <= bv_unsigned y < spZ regs) -> mem1 y = mem y) /\
  pstr_frame_at W mem1 regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U mem1) md1 0 /\
  ARU tfibsegs B ly S U W mem1 md1.

Lemma pstr_scan_loop : forall ly S U W regs mem md q ot text len p (tb : list byte) tcap Q Qp,
  FSupoisonU.fs_heads B ly S U ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  plain_run tb text len p Q ->
  Z.of_nat (length tb) = len -> text <= p -> 0 < text ->
  (forall k (cb : byte), nth_error tb (Z.to_nat k) = Some cb -> 0 <= k ->
     mbyte tfibsegs (mrestrict (w_H W) mem) (text + k) = Some cb) ->
  alloc_ceiling + STK_parse_string <= spZ regs ->
  (forall regsC memC mdC, pstr_call_facts B ly S U W regs mem md ot q p Q regsC memC mdC ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_malloc regsC memC mdC) Qp) ->
  forall i regs1 mem1 md1, 0 <= i <= Q ->
  pstr_loop_at ly S U W regs mem md ot q p text len (p + 1 + i) regs1 mem1 md1 ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs PSTR_SCAN regs1 mem1 md1) Qp.
Proof.
intros ly S U W regs mem md q ot text len p tb tcap Q Qp FH HTX HPR Hlen Htp Ht0 HTB Hsp HK.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_wx as HWX. pose proof asan_consts as (C1 & _).
pose proof HTX as (Htx1 & Hblk & Htx3).
pose proof Hblk as (Hin & Hal16 & Hpos & _).
pose proof HPR as (HQ0 & HQend & HQq & HQp).
intros i regs1 mem1 md1 Hi HL.
remember (Z.to_nat (Q - i)) as n eqn:Hn. revert i regs1 mem1 md1 Hi HL Hn.
induction n as [n IH] using lt_wf_ind.
intros i regs1 mem1 md1 Hi HL Hn.
destruct HL as (H10 & H11 & H12 & H20 & H8 & H9 & H22 & H23 & H24 & H3 & H4 & Hsp1 & Hmem1 & Hfr1 & HJ & HARU).
(* the byte at the cursor *)
assert (Hbyte : exists cb : byte, nth_error tb (Z.to_nat (p + 1 + i - text)) = Some cb /\
  32 <= bv_unsigned cb < 256 /\ (bv_unsigned cb = 34 <-> i = Q) /\ bv_unsigned cb <> 92).
{ destruct (Z.eq_dec i Q) as [->|Hne].
  - exists (Z_to_bv 8 34). split; [exact HQq|].
    assert (E34 : bv_unsigned (Z_to_bv 8 34 : byte) = 34)
      by (rewrite Z_to_bv_unsigned; change (bv_modulus 8) with 256; reflexivity).
    rewrite E34. split; [lia|]. split; [split; intros; reflexivity | lia].
  - destruct (HQp i ltac:(lia)) as (cb & Hnth & Hpb). exists cb. split; [exact Hnth|].
    pose proof (bv_unsigned_in_range 8 cb) as Hr. change (bv_modulus 8) with 256 in Hr.
    destruct Hpb as (Hp1 & Hp2 & Hp3). split; [lia|]. split; [split; intros Hq; [lia | lia] | lia]. }
destruct Hbyte as (cb & Hnth & Hcrange & Hc34 & Hc92).
set (c := bv_unsigned cb) in *.
set (x := p + 1 + i) in *.
(* its address and value on the machine's memory at this step *)
assert (Hxlo : text <= x) by lia.
assert (Hxhi : x < text + len) by lia.
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v))
  by (vm_compute; reflexivity).
assert (HEAD16 : HEAD = 16) by reflexivity.
assert (Hbb : text + tcap <= alloc_ceiling).
{ pose proof (al_blocks _ _ LAWS ly S W (unpoison U mem1) md1 (text - HEAD) (tcap + HEAD)
    (proj1 HARU) Hin) as (_ & _ & Hceil & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  unfold HEAD in Hceil, Hrq, Htx1. lia. }
assert (HxRT : RTLO <= x <= RTHI) by (unfold RTLO, RTHI; unfold HEAD in Htx1; lia).
assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold RTLO, RTHI in HxRT; lia).
assert (HFR : FRAME_PSTR = 144) by (vm_compute; reflexivity).
assert (Hxsp : ~ (spZ regs - FRAME_PSTR <= x < spZ regs)) by lia.
assert (Hvm : mbyte tfibsegs (mrestrict (w_H W) mem1) x = Some cb).
{ assert (Hm : mbyte tfibsegs (mrestrict (w_H W) mem) x = Some cb)
    by (replace x with (text + (x - text)) by lia; apply HTB; [|lia];
        replace (text + (x - text) - text) with (x - text) by lia; exact Hnth).
  revert Hm. unfold mbyte, mrestrict. rewrite (Hmem1 (Z_to_bv 64 x)); [auto|].
  rewrite (wz x Hx64). exact Hxsp. }
assert (Hval : val_mem tfibsegs (mrestrict (w_H W) mem1) x 1 c) by exact (pstr_val1 _ _ _ Hvm).
assert (HtlRT : RTLO <= text + len <= RTHI) by (unfold RTLO, RTHI; unfold HEAD in Htx1; lia).
assert (HppRT : RTLO <= p + 1 <= RTHI) by (unfold RTLO, RTHI; unfold HEAD in Htx1; lia).
pose proof (pstr_ssL_ok W regs1 mem1 x c (text + len) (p + 1) H10 H11 H12 H20 H23 HxRT HtlRT HppRT
  ltac:(lia) Hval) as HS.
assert (SHOK : sh_ok tfibsegs pstr_BxL (@nil shent) (Ereg regs1 [w64 c]) (mrestrict (w_H W) mem1))
  by apply Forall_nil.
unfold YG0d.cfg_at. change (w64 PSTR_SCAN) with (Z_to_bv 64 PSTR_SCAN).
assert (EU23 : YP0e.U (Ereg regs1 [w64 c]) pstr_BxL = SHADOW_OFF).
{ unfold pstr_BxL. apply (U_atom _ 23 SHADOW_OFF);
  [rewrite (ew_Ereg_nat regs1 [w64 c] 23 23%bv eq_refl); exact H23 | unfold SHADOW_OFF; lia]. }
assert (EU10 : YP0e.U (Ereg regs1 [w64 c]) (SOff 10 0) = x).
{ apply (U_atom _ 10 x); [rewrite (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl); exact H10 | lia]. }
(* 0x855c8 -> the quote test 0x855dc: the 1-byte shadow check of the cursor, the byte *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ rewrite EU23, EU10. cbn [ms_mem mkst].
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  refine (pstr_RA_blk_mem B ly S U W mem1 md1 (text - HEAD) (tcap + HEAD) x 1 HARU FH Hin _ _ _);
    unfold HEAD in *; lia. }
{ unfold pstr_ssL. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
- (* the byte is the closing quote: i = Q, and the run reaches the fuzz_malloc call *)
  pstr_env HS Eqa.
  assert (HAE : env_agree 33 (Ereg regs1 [w64 c]) Eqa)
    by (unfold Eqa; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
  assert (A32 : ew Eqa 32 = Z_to_bv 64 c)
    by (rewrite (proj1 HAE 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (pstr_byte_eq_dec Eqa c true A32 ltac:(lia) Hc) as Hqq.
  assert (HiQ : i = Q) by (apply Hc34; apply Z.eqb_eq; exact Hqq).
  (* 0x855dc -> 0x8560c .. 0x85614 `jal fuzz_malloc`: the run stops at the callee's entry *)
  fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  pstr_env HS Eqb.
  assert (HAE2 : env_agree 33 (Ereg regs1 [w64 c]) Eqb)
    by (unfold Eqb; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
  assert (B10 : ew Eqb 10 = Z_to_bv 64 x)
    by (rewrite (proj1 HAE2 10%nat ltac:(lia)), (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl); exact H10).
  assert (B20 : ew Eqb 20 = Z_to_bv 64 (p + 1))
    by (rewrite (proj1 HAE2 20%nat ltac:(lia)), (ew_Ereg_nat regs1 [w64 c] 20 20%bv eq_refl); exact H20).
  assert (Hmemeq : forall y, ms_mem ms0 y = mem1 y).
  { intros y. rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF0 y).
    exact (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF y). }
  assert (R1 : getr (ms_regs ms0) 1 = Z_to_bv 64 RA_PSTR_MALLOC)
    by (eapply fsw_reg_lit; [exact HS | vm_compute; reflexivity | unfold RA_PSTR_MALLOC; lia]).
  assert (R10 : getr (ms_regs ms0) 10 = w64 (Q + 1)).
  { lazymatch type of HS with st_ok _ _ ?SS _ =>
      assert (Hsr10 : sr_get (ss_regs SS) 10%bv
        = SAlu ALU_ADD (SOff 10 1) (SMd M_MUL (SOff 20 0) (SLit (2 ^ 64 - 1)))) by (vm_compute; reflexivity) end.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eqb _ ms0 10%bv HS), Hsr10.
    rewrite denot_lit_U, (pstr_len_val Eqb x (p + 1) B10 B20 ltac:(lia) ltac:(unfold RTLO, RTHI in HxRT; lia)
      ltac:(lia)).
    unfold w64. f_equal. lia. }
  assert (R2 : getr (ms_regs ms0) 2 = getr regs1 2)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 2%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R3 : getr (ms_regs ms0) 3 = getr regs1 3)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 3%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R4 : getr (ms_regs ms0) 4 = getr regs1 4)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 4%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R8 : getr (ms_regs ms0) 8 = getr regs1 8)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 8%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R9 : getr (ms_regs ms0) 9 = getr regs1 9)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 9%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R20 : getr (ms_regs ms0) 20 = getr regs1 20)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 20%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R22 : getr (ms_regs ms0) 22 = getr regs1 22)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 22%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R23 : getr (ms_regs ms0) 23 = getr regs1 23)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 23%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R24 : getr (ms_regs ms0) 24 = getr regs1 24)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 24%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eqb _ ms0 HS ltac:(vm_compute; reflexivity)) as Hms0.
  cbn [ss_pc] in Hms0. rewrite Hms0.
  apply (HK (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md1) mat0 md1)).
  unfold pstr_call_facts.
  split; [unfold spZ; rewrite R2; exact Hsp1|].
  split; [exact R1|]. split; [exact R10|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|].
  split; [rewrite R8; exact H8|]. split; [rewrite R9; exact H9|].
  split; [rewrite R20; exact H20|]. split; [rewrite R22; exact H22|].
  split; [rewrite R23; exact H23|]. split; [rewrite R24; exact H24|].
  split; [intros y Hy; rewrite (Hmemeq y); exact (Hmem1 y Hy)|].
  split; [exact (pstr_frame_at_eq W mem1 (ms_mem ms0) regs _ Hmemeq Hfr1)|].
  split; [exact HJ | exact HARU].
- (* a plain byte: i < Q, one more iteration *)
  pstr_env HS Epa.
  assert (HAE : env_agree 33 (Ereg regs1 [w64 c]) Epa)
    by (unfold Epa; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
  assert (A32 : ew Epa 32 = Z_to_bv 64 c)
    by (rewrite (proj1 HAE 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (pstr_byte_eq_dec Epa c false A32 ltac:(lia) Hc) as Hqq.
  assert (HiQ : i < Q) by (assert (c <> 34) by (apply Z.eqb_neq; exact Hqq); lia).
  assert (A10 : ew Epa 10 = Z_to_bv 64 x)
    by (rewrite (proj1 HAE 10%nat ltac:(lia)), (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl); exact H10).
  assert (A11 : ew Epa 11 = Z_to_bv 64 (text + len))
    by (rewrite (proj1 HAE 11%nat ltac:(lia)), (ew_Ereg_nat regs1 [w64 c] 11 11%bv eq_refl); exact H11).
  (* the byte is plain, so it is not a backslash *)
  assert (Hc92' : c <> 92) by exact Hc92.
  (* 0x855dc -> the cursor-overflow test 0x855f0 *)
  fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
  1:{ (* ~x < 1: the cursor does not wrap, so the trap 0x85a90 is not reached *)
      exfalso. fold Epa in Hc0. revert Hc0. rewrite branch_ltu_U.
      rewrite (U_not Epa 10 x A10 ltac:(lia)), (pstr_step_val Epa c A32 ltac:(lia) Hc92').
      replace (2 ^ 64 - 1 - x <? 1) with false
        by (symmetry; apply Z.ltb_ge; unfold RTLO, RTHI in HxRT; lia). discriminate. }
  (* 0x855f0 -> the loop's back branch 0x855f8 *)
  fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
  2:{ (* the cursor is still below in->end, so this arm is impossible *)
      exfalso. fold Epa in Hc1. revert Hc1. rewrite branch_ltu_U.
      rewrite (pstr_loop_cond_val Epa c x A32 ltac:(lia) Hc92' A10 ltac:(lia)
        ltac:(unfold RTLO, RTHI in HxRT; lia)).
      rewrite (U_atom Epa 11 (text + len) A11 ltac:(unfold RTLO, RTHI in HtlRT; lia)).
      replace (x + 1 <? text + len) with true by (symmetry; apply Z.ltb_lt; lia). discriminate. }
  (* 0x855f8 -> the loop head 0x855c8, with the cursor one byte on *)
  fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan PSTR_SCAN.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (Hmemeq : forall y, ms_mem ms2 y = mem1 y).
  { intros y. rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF2 y).
    rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF1 y).
    rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF0 y).
    exact (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF y). }
  assert (N10 : getr (ms_regs ms2) 10 = w64 (x + 1)).
  { lazymatch type of HS with st_ok _ _ ?SS _ =>
      assert (Hsr10 : sr_get (ss_regs SS) 10%bv
        = SAlu ALU_ADD (SOff 10 0) (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1)))
        by (vm_compute; reflexivity) end.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) Epa _ ms2 10%bv HS), Hsr10, denot_lit_U.
    rewrite (pstr_loop_cond_val Epa c x A32 ltac:(lia) Hc92' A10 ltac:(lia)
      ltac:(unfold RTLO, RTHI in HxRT; lia)). reflexivity. }
  assert (N12 : getr (ms_regs ms2) 12 = w64 34)
    by (eapply fsw_reg_lit; [exact HS | vm_compute; reflexivity | lia]).
  assert (N2 : getr (ms_regs ms2) 2 = getr regs1 2)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 2%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N3 : getr (ms_regs ms2) 3 = getr regs1 3)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 3%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N4 : getr (ms_regs ms2) 4 = getr regs1 4)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 4%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N8 : getr (ms_regs ms2) 8 = getr regs1 8)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 8%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N9 : getr (ms_regs ms2) 9 = getr regs1 9)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 9%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N11 : getr (ms_regs ms2) 11 = getr regs1 11)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 11%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N20 : getr (ms_regs ms2) 20 = getr regs1 20)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 20%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N22 : getr (ms_regs ms2) 22 = getr regs1 22)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 22%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N23 : getr (ms_regs ms2) 23 = getr regs1 23)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 23%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N24 : getr (ms_regs ms2) 24 = getr regs1 24)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms2 24%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Epa _ ms2 HS ltac:(vm_compute; reflexivity)) as Hms2.
  cbn [ss_pc] in Hms2. rewrite Hms2.
  refine (IH (Z.to_nat (Q - (i + 1))) ltac:(lia) (i + 1) (ms_regs ms2) (ms_mem ms2) _ ltac:(lia) _ eq_refl).
  unfold pstr_loop_at.
  split; [replace (p + 1 + (i + 1)) with (x + 1) by lia; exact N10|].
  split; [rewrite N11; exact H11|]. split; [exact N12|].
  split; [rewrite N20; exact H20|].
  split; [rewrite N8; exact H8|]. split; [rewrite N9; exact H9|].
  split; [rewrite N22; exact H22|]. split; [rewrite N23; exact H23|].
  split; [rewrite N24; exact H24|].
  split; [rewrite N3; exact H3|]. split; [rewrite N4; exact H4|].
  split; [unfold spZ; rewrite N2; exact Hsp1|].
  split; [intros y Hy; rewrite (Hmemeq y); exact (Hmem1 y Hy)|].
  split; [exact (pstr_frame_at_eq W mem1 (ms_mem ms2) regs _ Hmemeq Hfr1)|].
  split; [exact HJ | exact HARU].
Qed.

(* ---- one saved register of the prologue's frame, read out of the entry run's stack region ---- *)
Lemma pstr_slot : forall (W : world tfibsegs) regs extra E (m : word -> option byte) cs (off rr : Z) (k : nat)
    (rb : bv 5),
  env_agree 33 (Ereg regs extra) E ->
  region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) (- FRAME_PSTR) 0 (- FRAME_PSTR) 0 cs) ->
  In (YP09.mkChunk (off - FRAME_PSTR) (CVal 8 (SOff k 0))) cs ->
  Z.of_nat k = bv_unsigned rb -> (k < 33)%nat -> rr = bv_unsigned rb ->
  val_mem tfibsegs m (spZ regs - FRAME_PSTR + off) 8 (bv_unsigned (YK11.getr regs (Z_to_bv 5 rr))).
Proof.
intros W regs extra E m cs off rr k rb HAE HR Hin Hk Hk33 Hrr.
assert (Esp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (proj1 HAE 2%nat ltac:(lia)), (ew_Ereg_nat regs extra 2 2%bv eq_refl); reflexivity).
replace (spZ regs - FRAME_PSTR + off) with (spZ regs + (off - FRAME_PSTR)) by lia.
eapply (fsw_field E m 2%nat (spZ regs) cs (- FRAME_PSTR) 0 (- FRAME_PSTR) 0
  (off - FRAME_PSTR) 8%N (SOff k 0));
  [exact HR | exact Esp | exact Hin | | cbn [Z.of_N Z.mul]; apply u64_range | cbn [Z.of_N]; lia].
rewrite fsw_SOff0, (proj1 HAE k Hk33), (ew_Ereg_nat regs extra k rb Hk).
replace (Z_to_bv 5 rr) with rb by (rewrite Hrr; symmetry; apply Z_to_bv_bv_unsigned).
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- stage 1: the entry 0x85534 -> the fuzz_malloc call 0x85614 ---- *)
Definition pstr_gf_q : list (nat * afact) := [(10%nat, mkAF RQLO RQHI 3)].
(* the reseat at 0x85594 (`ld s4, 0(s0)`): struct pj_in's two fields in->p and in->end as one region at s0 (atom 8;
   s1 = s0 + 8 is computed after the reseat, 0x855a4), every register its own atom, the shadow base in s7 (atom 23) *)
Definition pstr_reg_pe : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition pstr_facts1 : facts := mkFacts
  [(8%nat, mkAF RQLO RQHI 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF RTLO RTHI 0); (33%nat, mkAF RTLO RTHI 0)] [] [].
Definition pstr_ss1 : sstate := mkSS 0x85594 sr_atoms [pstr_reg_pe] None pstr_facts1.
Definition pstr_Bx1 : sv := SOff 23 0.

Lemma pstr_stage1 : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q Qp,
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  (forall regsC memC mdC, pstr_call_facts B ly S U W regs mem md ot q p Q regsC memC mdC ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_malloc regsC memC mdC) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_string regs mem md) Qp.
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q Qp HPRE FH H10 HIN HWIN HTX Hplt Hpq HPR HK.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_wx as HWX. pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAPU & HRO).
pose proof (fsw_ARU B STK_parse_string ly S U W regs mem md ch HAPU) as HARU.
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_parse_string ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HWIN as (Hq1 & Hq2 & Hotal & Hottop & Hotpres).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq1 & Bt0 & Bp & Btl & Bdis & Blen & Bqal & Bd).
pose proof HTX as (Htx1 & Hblk & Htx3).
pose proof Hblk as (Hin & Hal16t & Hpos & _).
pose proof HPR as (HQ0 & HQend & HQq & HQp).
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v))
  by (vm_compute; reflexivity).
assert (HEAD16 : HEAD = 16) by reflexivity.
pose proof Hstk as (_ & _ & Hlylo & Hlyslo & Hlyshi & Hly47 & _ & Hlytop & Hlyhi).
(* the bytes of the text, as the walk reads them *)
assert (HTB : forall k (cb : byte), nth_error tb (Z.to_nat k) = Some cb -> 0 <= k ->
  mbyte tfibsegs (mrestrict (w_H W) mem) (text + k) = Some cb)
  by (intros k cb Hk Hk0; exact (pstr_text_byte W mem q text len p d tb k cb HIN Hk Hk0)).
(* the entry state and the journal at the raised window top *)
assert (HSE : st_ok tfibsegs (Ereg regs fs_extraT) (fss0T_args A_parse_string FRAME_PSTR [] pstr_gf_q)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_parse_string) mem (YK11.seg_rom tfibsegs)))).
{ assert (Esp0 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
    by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
  eapply (fsw_entryT_args B STK_parse_string FRAME_PSTR ly S U W regs mem md ch A_parse_string [] pstr_gf_q
    TL_got TL_cell HAPU ltac:(vm_compute; split; discriminate) ltac:(vm_compute; reflexivity) (Forall_nil _)).
  - apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Esp0.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    change FRAME_PSTR with 144.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - unfold pstr_gf_q. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl), H10. unfold w64.
    rewrite (wz q ltac:(lia)). unfold RQLO, RQHI. change (2 ^ 3) with 8.
    split; [|exact I]. split; [lia | split; [exact Bqal | lia]]. }
pose proof (fsw_ajournal_init_ot B STK_parse_string FS_PSTAT_FP ly S U W regs mem md ch ot HAPU
  ltac:(lia) Hotal ltac:(lia) Hotpres) as HJ.
assert (SHOK : sh_ok tfibsegs fs_Bx (@nil shent) (Ereg regs fs_extraT) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (EB32 : YP0e.U (Ereg regs fs_extraT) fs_Bx = SHADOW_OFF).
{ unfold fs_Bx. apply (U_atom _ 32 SHADOW_OFF);
  [change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]. }
assert (EB10 : forall z, 0 <= q + z < 2 ^ 64 -> YP0e.U (Ereg regs fs_extraT) (SOff 10 z) = q + z).
{ intros z Hz. apply (U_atom_off _ 10 q z);
  [rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact H10 | lia | lia]. }
unfold YG0d.cfg_at. change (w64 A_parse_string) with (Z_to_bv 64 A_parse_string).
(* 0x85534 -> 0x85594: the prologue, the alignment check, the shadow base, the shadow check of in->p *)
fsw_aj_run_tokU parse_string_tbl_ok HSE HJ HARU SHOK fs_Bspan.
{ rewrite EB32, (EB10 0 ltac:(lia)). cbn [ms_mem mkst]. rewrite Z.add_0_r.
  exact (pstr_RA_stk_mem B ly S U W mem md q 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bqal
    ltac:(reflexivity) ltac:(lia)). }
{ unfold fss0T_args, fsT_regions_args, fsT_regions. cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity
    | rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); unfold spZ; lia
    | unfold fstk; cbn [YP09.r_wlo]; change FRAME_PSTR with 144; lia
    | unfold fstk; cbn [YP09.r_whi]; lia
    | apply awr_ok_cons_ro; [unfold fs_got_region; cbn; lia|];
      apply awr_ok_cons_ro; [unfold fs_bcell_region; cbn; lia | apply awr_ok_nil]]. }
pstr_env HSE Ee.
assert (HAEe : env_agree 33 (Ereg regs fs_extraT) Ee)
  by (unfold Ee; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
assert (Ee10 : ew Ee 10 = Z_to_bv 64 q)
  by (rewrite (proj1 HAEe 10%nat ltac:(lia)), (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact H10).
assert (Ee32 : ew Ee 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (proj1 HAEe 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
(* the machine state at 0x85594 *)
assert (M8 : getr (ms_regs ms) 8 = w64 q).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 8%bv = SOff 10 0) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 8%bv HSE), Hsr, fsw_SOff0, Ee10. reflexivity. }
assert (M23 : getr (ms_regs ms) 23 = w64 SHADOW_OFF).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 23%bv = SOff 32 0) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 23%bv HSE), Hsr, fsw_SOff0, Ee32. reflexivity. }
assert (M22 : getr (ms_regs ms) 22 = w64 (SHADOW_OFF + q / 8)).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 22%bv
      = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 22%bv HSE), Hsr,
    (pstr_shx Ee 10 32 0 q SHADOW_OFF Ee10 Ee32 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia)). rewrite Z.add_0_r. reflexivity. }
assert (M2 : bv_unsigned (getr (ms_regs ms) 2) = spZ regs - FRAME_PSTR).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 2%bv = SOff 2 (- FRAME_PSTR)) by (vm_compute; reflexivity) end.
  eapply (fsw_reg_off (w_H W) Ee _ ms 2%bv 2 (- FRAME_PSTR) (spZ regs));
    [exact HSE | exact Hsr | rewrite (proj1 HAEe 2%nat ltac:(lia)), (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
      reflexivity | change FRAME_PSTR with 144; lia]. }
assert (M3 : getr (ms_regs ms) 3 = getr regs 3)
  by (apply (pstr_reg_keep (w_H W) Ee _ ms 3%bv regs fs_extraT HSE HAEe); [vm_compute; reflexivity | vm_compute; lia]).
assert (M4 : getr (ms_regs ms) 4 = getr regs 4)
  by (apply (pstr_reg_keep (w_H W) Ee _ ms 4%bv regs fs_extraT HSE HAEe); [vm_compute; reflexivity | vm_compute; lia]).
(* memory: the prologue wrote only the frame *)
assert (Hmem1 : forall y : word, ~ (spZ regs - FRAME_PSTR <= bv_unsigned y < spZ regs) -> ms_mem ms y = mem y).
{ intros y Hy. apply HF. intros (r0 & Hr0 & Hr).
  unfold fss0T_args, fsT_regions_args, fsT_regions in Hr0. cbn [ss_mem app In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[]]]];
    [ unfold fstk in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hr;
      change FRAME_PSTR with 144 in *; apply Hy; unfold spZ; lia
    | unfold fs_got_region in Hr; cbn in Hr; lia
    | unfold fs_bcell_region in Hr; cbn in Hr; lia ]. }
(* the 13 saved words *)
assert (Hfr1 : pstr_frame_at W (ms_mem ms) regs (spZ regs - FRAME_PSTR)).
{ pose proof (fsw_region_nth Ee _ _ 0%nat _ HSE ltac:(vm_compute; reflexivity)) as HR0.
  cbn [ms_mem restrict mkst] in HR0.
  unfold pstr_frame_at, pstr_saved.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [..|apply Forall_nil];
    first
    [ exact (pstr_slot W regs fs_extraT Ee _ _ 0x88 1 1%nat 1%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x80 8 8%nat 8%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x78 9 9%nat 9%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x70 18 18%nat 18%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x68 19 19%nat 19%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x60 20 20%nat 20%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x58 21 21%nat 21%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x50 22 22%nat 22%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x48 23 23%nat 23%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x40 24 24%nat 24%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x38 25 25%nat 25%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x30 26 26%nat 26%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl)
    | exact (pstr_slot W regs fs_extraT Ee _ _ 0x28 27 27%nat 27%bv HAEe HR0 ltac:(cbv [In]; tauto) eq_refl ltac:(lia) eq_refl) ]. }
(* the two fields of struct pj_in, on the machine's memory after the prologue *)
assert (Vp : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) q 8 p).
{ apply (pstr_val_mem_eq_at _ mem (ms_mem ms) q 8 p);
    [intros k Hk; apply Hmem1; rewrite (wz (q + Z.of_nat k) ltac:(lia)); lia|].
  pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) q (Z_to_bv 64 p) (proj1 HIN)) as Hw.
  rewrite (wz p ltac:(lia)) in Hw.
  exact (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem) q p) Hw). }
assert (Ve : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + 8) 8 (text + len)).
{ apply (pstr_val_mem_eq_at _ mem (ms_mem ms) (q + 8) 8 (text + len));
    [intros k Hk; apply Hmem1; rewrite (wz (q + 8 + Z.of_nat k) ltac:(lia)); lia|].
  pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) (q + 8) (Z_to_bv 64 (text + len))
    (proj1 (proj2 HIN))) as Hw.
  rewrite (wz (text + len) ltac:(lia)) in Hw.
  exact (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem) (q + 8) (text + len)) Hw). }
(* the reseat at 0x85594: struct pj_in's two fields as one region at s0, every register its own atom *)
assert (HQRQ : RQLO <= q <= RQHI) by (unfold RQLO, RQHI; lia).
assert (HLRT : RTLO <= text + len <= RTHI).
{ pose proof (al_blocks _ _ LAWS ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR Hin)
    as (_ & _ & Hcl & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(lia)) as (_ & Hrq).
  unfold RTLO, RTHI. lia. }
assert (HPRT : RTLO <= p <= RTHI) by (unfold RTLO, RTHI in HLRT |- *; lia).
assert (HS1 : st_ok tfibsegs (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) pstr_ss1
  (restrict (w_H W) (YK11.mkst (ms_regs ms) (Z_to_bv 64 0x85594) (ms_mem ms) (YK11.seg_rom tfibsegs)))).
{ assert (G8 : bv_unsigned (ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 8) = q)
    by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl), M8; unfold w64; apply wz; lia).
  assert (G23 : bv_unsigned (ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 23) = SHADOW_OFF)
    by (rewrite (ew_Ereg_nat (ms_regs ms) _ 23 23%bv eq_refl), M23; unfold w64; apply wz;
        unfold SHADOW_OFF; lia).
  assert (G32 : ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 32 = Z_to_bv 64 p)
    by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G33 : ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 33 = Z_to_bv 64 (text + len))
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite restrict_mkst_fx. unfold pstr_ss1. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold pstr_reg_pe, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite G8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 32 0) p);
        [rewrite fsw_SOff0, G32; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Vp].
    + apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff 33 0) (text + len));
        [rewrite fsw_SOff0, G33; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Ve].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I]. unfold pstr_facts1. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite G8, G23, G32, G33.
    rewrite (wz p ltac:(unfold RTLO, RTHI in HPRT; lia)),
      (wz (text + len) ltac:(unfold RTLO, RTHI in HLRT; lia)).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r.
    split; [split; [unfold RQLO, RQHI in *; lia | split; [exact Bqal | lia]]|].
    split; [split; [unfold SHADOW_OFF; lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I]. }
assert (SHOK1 : sh_ok tfibsegs pstr_Bx1 (@nil shent)
  (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) (mrestrict (w_H W) (ms_mem ms))) by apply Forall_nil.
assert (EU23 : YP0e.U (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) pstr_Bx1 = SHADOW_OFF).
{ unfold pstr_Bx1. apply (U_atom _ 23 SHADOW_OFF);
  [rewrite (ew_Ereg_nat (ms_regs ms) _ 23 23%bv eq_refl); exact M23 | unfold SHADOW_OFF; lia]. }
assert (EU8 : YP0e.U (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) (SOff 8 8) = q + 8).
{ apply (U_atom_off _ 8 q 8); [rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact M8 | lia | lia]. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Ee _ ms HSE ltac:(vm_compute; reflexivity)) as Hmsf.
cbn [ss_pc] in Hmsf. rewrite Hmsf.
clear SHOK HSE.
(* 0x85594 -> the exit test 0x855bc: in->p, in->p + 1 < 2 (decided), the shadow check of in->end, in->end *)
fsw_aj_run_tokU parse_string_tbl_ok HS1 HJ HARU SHOK1 fs_Bspan.
{ rewrite EU23, EU8. cbn [ms_mem mkst].
  refine (pstr_RA_stk_mem B ly S U W _ _ (q + 8) 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _
    ltac:(reflexivity) ltac:(lia)).
  rewrite Zplus_mod, Bqal. reflexivity. }
{ unfold pstr_ss1. cbn [ss_mem].
  apply awr_ok_cons_ro; [unfold pstr_reg_pe; cbn; lia | apply awr_ok_nil]. }
srr_branch_tok parse_string_tbl_ok HS1 SHOK1 fs_Bspan.
{ (* in->p + 1 is below in->end, so the exit 0x85a1c is not taken *)
  exfalso. pstr_env HS1 Eg. fold Eg in Hc.
  assert (HAEg : env_agree 34 (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) Eg)
    by (unfold Eg; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
  assert (G32' : ew Eg 32 = Z_to_bv 64 p)
    by (rewrite (proj1 HAEg 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra;
        reflexivity).
  assert (G33' : ew Eg 33 = Z_to_bv 64 (text + len))
    by (rewrite (proj1 HAEg 33%nat ltac:(lia)); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra;
        reflexivity).
  revert Hc. rewrite branch_geu_U.
  rewrite (U_atom_off Eg 32 p 1 G32' ltac:(unfold RTLO, RTHI in HPRT; lia)
    ltac:(unfold RTLO, RTHI in HPRT; lia)).
  rewrite (U_atom Eg 33 (text + len) G33' ltac:(unfold RTLO, RTHI in HLRT; lia)).
  replace (p + 1 <? text + len) with true by (symmetry; apply Z.ltb_lt; lia). discriminate. }
(* 0x855bc -> the scan loop head 0x855c8 *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS1 HJ HARU SHOK1 fs_Bspan PSTR_SCAN.
{ cbn [add_cond ss_mem]. unfold pstr_ss1. cbn [ss_mem].
  apply awr_ok_cons_ro; [unfold pstr_reg_pe; cbn; lia | apply awr_ok_nil]. }
pstr_env HS1 Eh.
assert (HAEh : env_agree 34 (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) Eh)
  by (unfold Eh; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
assert (H32h : ew Eh 32 = Z_to_bv 64 p)
  by (rewrite (proj1 HAEh 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (H33h : ew Eh 33 = Z_to_bv 64 (text + len))
  by (rewrite (proj1 HAEh 33%nat ltac:(lia)); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (H8h : ew Eh 8 = Z_to_bv 64 q)
  by (rewrite (proj1 HAEh 8%nat ltac:(lia)), (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact M8).
assert (H23h : ew Eh 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (proj1 HAEh 23%nat ltac:(lia)), (ew_Ereg_nat (ms_regs ms) _ 23 23%bv eq_refl); exact M23).
assert (L10 : getr (ms_regs ms1) 10 = w64 (p + 1)).
{ lazymatch type of HS1 with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 10%bv = SOff 32 1) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eh _ ms1 10%bv HS1), Hsr, denot_lit_U,
    (U_atom_off Eh 32 p 1 H32h ltac:(unfold RTLO, RTHI in HPRT; lia) ltac:(unfold RTLO, RTHI in HPRT; lia)).
  reflexivity. }
assert (L20 : getr (ms_regs ms1) 20 = w64 (p + 1)).
{ lazymatch type of HS1 with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 20%bv = SOff 32 1) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eh _ ms1 20%bv HS1), Hsr, denot_lit_U,
    (U_atom_off Eh 32 p 1 H32h ltac:(unfold RTLO, RTHI in HPRT; lia) ltac:(unfold RTLO, RTHI in HPRT; lia)).
  reflexivity. }
assert (L11 : getr (ms_regs ms1) 11 = w64 (text + len)).
{ lazymatch type of HS1 with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 11%bv = SOff 33 0) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eh _ ms1 11%bv HS1), Hsr, fsw_SOff0, H33h. reflexivity. }
assert (L12 : getr (ms_regs ms1) 12 = w64 34)
  by (eapply fsw_reg_lit; [exact HS1 | vm_compute; reflexivity | lia]).
assert (L9 : getr (ms_regs ms1) 9 = w64 (q + 8)).
{ lazymatch type of HS1 with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 9%bv = SOff 8 8) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eh _ ms1 9%bv HS1), Hsr, denot_lit_U,
    (U_atom_off Eh 8 q 8 H8h ltac:(lia) ltac:(lia)).
  reflexivity. }
assert (L24 : getr (ms_regs ms1) 24 = w64 (SHADOW_OFF + (q + 8) / 8)).
{ lazymatch type of HS1 with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 24%bv
      = SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 23 0)) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eh _ ms1 24%bv HS1), Hsr,
    (pstr_shx Eh 8 23 8 q SHADOW_OFF H8h H23h ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia)). reflexivity. }
assert (L2 : getr (ms_regs ms1) 2 = getr (ms_regs ms) 2)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 2%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L3 : getr (ms_regs ms1) 3 = getr (ms_regs ms) 3)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 3%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L4 : getr (ms_regs ms1) 4 = getr (ms_regs ms) 4)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 4%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L8 : getr (ms_regs ms1) 8 = getr (ms_regs ms) 8)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 8%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L22 : getr (ms_regs ms1) 22 = getr (ms_regs ms) 22)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 22%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L23 : getr (ms_regs ms1) 23 = getr (ms_regs ms) 23)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 23%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (Hmem2 : forall y, ms_mem ms1 y = ms_mem ms y).
{ intros y. rewrite (pstr_frame_none _ pstr_reg_pe _ _ ltac:(unfold pstr_reg_pe; cbn; lia) HF1 y).
  exact (pstr_frame_none _ pstr_reg_pe _ _ ltac:(unfold pstr_reg_pe; cbn; lia) HF0 y). }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eh _ ms1 HS1 ltac:(vm_compute; reflexivity)) as Hmsg.
cbn [ss_pc] in Hmsg. rewrite Hmsg.
refine (pstr_scan_loop ly S U W regs mem md q ot text len p tb tcap Q Qp FH HTX HPR Blen ltac:(lia)
  ltac:(lia) HTB ltac:(lia) HK 0 (ms_regs ms1) (ms_mem ms1) _ ltac:(lia) _).
unfold pstr_loop_at.
split; [replace (p + 1 + 0) with (p + 1) by lia; exact L10|].
split; [exact L11|]. split; [exact L12|]. split; [exact L20|].
split; [rewrite L8; exact M8|]. split; [exact L9|].
split; [rewrite L22; exact M22|]. split; [rewrite L23; exact M23|]. split; [exact L24|].
split; [rewrite L3; exact M3|]. split; [rewrite L4; exact M4|].
split; [unfold spZ; rewrite L2; exact M2|].
split; [intros y Hy; rewrite (Hmem2 y); exact (Hmem1 y Hy)|].
split; [exact (pstr_frame_at_eq W (ms_mem ms) (ms_mem ms1) regs _ Hmem2 Hfr1)|].
split; [exact HJ | exact HARU].
Qed.
End W.

(* ================= the fuzz_malloc call 0x85614, its CTX-free halves =================
   The call step's two halves that need no In-CTX premise (owner-approved spec change, a Theorem Labs lane 2026-10-29 05:00Z:
   fuzz_malloc_spec's `In (raZ regs :: spine ch) CTX` premise is dropped; the call step and the composition
   `parse_string_proof : forall CTX, parse_string_spec CTX` follow when the new lib/B/FSH_Fn_alloc.v lands, as
   `eapply SRr_bind; [exact (MALLOC ... (pstr_call_pre ...)) | intros W' c' _ HP; exact (pstr_call_post ... HP)]`):
   - pstr_call_pre: from stage 1's call-site facts (pstr_call_facts) to fuzz_malloc_spec's other premises at the call:
     the chain moved to the call memory (pc_achain_agree), the callee's fpreU by FSW_ret's fsw_fpreU_atFP (the kit's
     FP-generic form), raZ = 0x85618 and fs_glob on the call memory;
   - pstr_call_post: from fuzz_malloc_spec's post at n = Q + 1 (pstr_malloc_post, its text) to stage 2's return-site
     facts (pstr_ret_facts), by the journal composition FSW_K3's fsw_rt_atU3 (its FP arm: the four statics are image
     bytes, pc_fp_img).
   Ported from image A's walk (9f3343583b7 lib/A/FSW_parse_string.v :2044-2251, pstr_call_step split at its step 3);
   B's registers at the call are s6 / s7 / s8 = x22 / x23 / x24 (lib/B/FSW_parse_string_defs.v). *)
Section W3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- helpers of the call step (prefix pc_) ---- *)
(* achain under a reader that agrees from v - 16 up to the stack top: fpchain reads only there (YCbq.v achain_kept
   needs agreement from sp up, which the prologue's frame [sp, sp + 144) breaks) *)
Lemma pc_achain_agree : forall ly (rd rd' : reader) sp v ch,
  achain ly rd sp v ch -> (forall a, v - 16 <= a < ly_top ly -> rd' a = rd a) -> achain ly rd' sp v ch.
Proof.
intros ly rd rd' sp v ch [H | (H1 & H2 & H3 & H4 & H5)] Hk; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (fpchain_ext (rdword rd) (rdword rd') v (ly_top ly) ch); [|lia|exact H4].
intros a Ha1 Ha2. apply rdword_ext. intros k Hk'. apply Hk. lia.
Qed.
(* FS_PSTAT_FP's four cells (lib/B/FSPstat.v) are image statics (in fs.asan-ubsan's last loaded segment, ps2_img_hi) *)
Lemma pc_fp_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). apply ps2_img_hi. unfold FS_PSTAT_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha; lia.
Qed.
(* Lib/Mem bytes_at through mbyte agreement *)
Lemma pc_bytes_at_keep : forall (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte tfibsegs m' (a + i) = mbyte tfibsegs m (a + i)) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs Hk (Ba & Bb & Bc). split; [exact Ba|]. split; [exact Bb|]. intros i Hi.
rewrite pstr_mrd_mbyte, (Hk (Z.of_nat i) ltac:(lia)), <- pstr_mrd_mbyte. exact (Bc i Hi).
Qed.
(* pj_in_ok through mbyte agreement on the struct and the text, and writability of the struct *)
Lemma pc_pj_in_ok_keep : forall (m m' : word -> option byte) q text len p d (tb : list byte),
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  (forall i, 0 <= i < 24 -> mbyte tfibsegs m' (q + i) = mbyte tfibsegs m (q + i)) ->
  (forall i, 0 <= i < 24 -> writable_at tfibsegs m' (q + i)) ->
  (forall i, 0 <= i < len -> mbyte tfibsegs m' (text + i) = mbyte tfibsegs m (text + i)) ->
  PjIn.pj_in_ok tfibsegs m' q text len p d tb.
Proof.
intros m m' q text len p d tb H Hq Hw Ht.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
destruct H4 as (W0 & W1 & _).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
- apply (pc_bytes_at_keep m m'); [|exact H1]. rewrite Mem.length_le8. intros i Hi. apply Hq. lia.
- apply (pc_bytes_at_keep m m'); [|exact H2]. rewrite Mem.length_le8. intros i Hi.
  rewrite <- Z.add_assoc. apply Hq. lia.
- apply (pc_bytes_at_keep m m'); [|exact H3]. rewrite Mem.length_le4. intros i Hi.
  rewrite <- Z.add_assoc. apply Hq. lia.
- split; [exact W0|]. split; [exact W1|]. intros i Hi. exact (Hw i Hi).
- apply (pc_bytes_at_keep m m'); [|exact H10]. rewrite H9. intros i Hi. apply Ht. lia.
Qed.

(* fuzz_malloc_spec's post (lib/B/FSH_Fn_alloc.v) at the call 0x85614: regs = regsC, mem = memC, n = Q + 1 *)
Definition pstr_malloc_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regsC : bvmap 5 word) (memC : word -> option byte) (mdC : Model) (Q live peak cnt fail : Z)
  : world tfibsegs -> config -> Prop :=
  fun W' c' =>
    (cnt = fail /\ apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regsC ly S W memC mdC 0 U U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          FSupoisonU.fs_heads B ly' S' U /\
          fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
    \/
    (cnt <> fail /\ exists res,
       apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regsC ly S W memC mdC 1 U (U ++ [(res - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
          ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, Q + 1 + HEAD)] /\
          FSupoisonU.fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
          (0 < Q + 1 -> fs_rblock tfibsegs B ly' S' W' mem' res (Q + 1)) /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF res (Q + 1) /\
          fs_glob tfibsegs W' mem' (live + (Q + 1)) (Z.max peak (live + (Q + 1))) (cnt + 1) fail) W' c').

(* ---- the call 0x85614, before: fuzz_malloc_spec's premises at the call, but its In-CTX one ---- *)
Lemma pstr_call_pre : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt fail
    regsC memC mdC chq,
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch ->
  achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs - FRAME_parse_string) q chq ->
  spZ regs + 16 <= q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb -> rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  pstr_call_facts B ly S U W regs mem md ot q p Q regsC memC mdC ->
  fpreU tfibsegs B STK_fuzz_malloc ly S U W regsC memC mdC chq /\ raZ regsC = RA_PSTR_MALLOC /\
  fs_glob tfibsegs W memC live peak cnt fail.
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC chq
  HPRE HCH Hq16 HIN HWIN HTX HPR HGL Hquiet HCF.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & _ & K3 & _).
destruct HCF as (Csp & C1r & C10 & C3r & C4r & C8 & C9 & C20 & C22 & C23 & C24 & CM & CF & CJ & CARU).
pose proof HPRE as (HAPU & HRO).
pose proof (fsw_ARU B STK_parse_string ly S U W regs mem md ch HAPU) as HARU0.
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_parse_string ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof Hstk as (_ & _ & _ & _ & _ & Hhi47 & _ & Htop1 & Htop2).
pose proof HWIN as (Hq1 & Hq2 & Hotal & Hottop & Hotpres).
pose proof HPR as (HQ0 & _).
pose proof Hquiet as (Hfail & Hcnt0 & Hcnt).
pose proof HTX as (Htx1 & (HTX1 & Htx16 & Htc & Htxv) & Hlen).
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v))
  by (vm_compute; reflexivity).
assert (HSTKm : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v))
  by (vm_compute; reflexivity).
assert (EH : HEAD = 16) by reflexivity.
assert (Hsc : spZ regsC = spZ regs - 144) by (rewrite Csp; reflexivity).
(* memC is mem outside the prologue's frame *)
assert (MC : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 144 \/ spZ regs <= a) ->
  memC (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hb. apply CM. rewrite wz by exact Ha. unfold FRAME_PSTR, FRAME_parse_string. lia. }
assert (SB : same_below mem memC alloc_ceiling) by (intros x Hx; apply MC; lia).
(* 1. the chain, carried to the call's memory *)
assert (Es0 : s0Z regsC = q) by (unfold s0Z; rewrite C8; unfold w64; apply wz; lia).
assert (HCHC : achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) (s0Z regsC) chq).
{ rewrite Es0, Csp. unfold FRAME_PSTR.
  apply (pc_achain_agree ly (aview tfibsegs (w_H W) (unpoison U mem))); [exact HCH|].
  intros a Ha. apply (aview_at tfibsegs). unfold unpoison. rewrite MC by lia. reflexivity. }
(* 2. the callee's fpreU *)
assert (Era : raZ regsC = RA_PSTR_MALLOC) by (unfold raZ; rewrite C1r; unfold w64, RA_PSTR_MALLOC; apply wz; lia).
assert (HPREc : fpreU tfibsegs B STK_fuzz_malloc ly S U W regsC memC mdC chq)
  by exact (fsw_fpreU_atFP B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S U W (unpoison U mem) md []
    ly S W memC mdC 0 regsC STK_fuzz_malloc (spZ regsC - ot) chq CJ CARU (arodata_below B W mem memC SB HRO)
    ltac:(lia) ltac:(rewrite Hsc; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite C1r; vm_compute; reflexivity) ltac:(rewrite Era; unfold RA_PSTR_MALLOC; lia)
    ltac:(rewrite C3r; exact Hgp) ltac:(rewrite C4r; exact Htp) HCHC).
assert (HGLc : fs_glob tfibsegs W memC live peak cnt fail) by exact (fs_glob_below W mem memC live peak cnt fail SB HGL).
split; [exact HPREc|]. split; [exact Era | exact HGLc].
Qed.

(* ---- the call 0x85614, after: from fuzz_malloc's post to stage 2's return-site facts ---- *)
Lemma pstr_call_post : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt fail
    regsC memC mdC (Qp : world tfibsegs -> config -> Prop) W' c',
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb -> rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  pstr_call_facts B ly S U W regs mem md ot q p Q regsC memC mdC ->
  (forall ly2 S2 W2 regs2 mem2 md2 a,
     pstr_ret_facts B ly S U W regs mem md ot q p d Q text len tcap live peak cnt fail a tb ly2 S2 W2 regs2 mem2 md2 ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2) Qp) ->
  pstr_malloc_post ly S U W regsC memC mdC Q live peak cnt fail W' c' ->
  SRr tfibsegs W' c' Qp.
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC Qp W' c'
  HPRE HIN HWIN HTX HPR HGL Hquiet HCF HK HMP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & _ & K3 & _).
destruct HCF as (Csp & C1r & C10 & C3r & C4r & C8 & C9 & C20 & C22 & C23 & C24 & CM & CF & CJ & CARU).
pose proof HPRE as (HAPU & HRO).
pose proof (fsw_ARU B STK_parse_string ly S U W regs mem md ch HAPU) as HARU0.
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_parse_string ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof Hstk as (_ & _ & _ & _ & _ & Hhi47 & _ & Htop1 & Htop2).
pose proof HWIN as (Hq1 & Hq2 & Hotal & Hottop & Hotpres).
pose proof HPR as (HQ0 & _).
pose proof Hquiet as (Hfail & Hcnt0 & Hcnt).
pose proof HTX as (Htx1 & (HTX1 & Htx16 & Htc & Htxv) & Hlen).
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v))
  by (vm_compute; reflexivity).
assert (HSTKm : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v))
  by (vm_compute; reflexivity).
assert (EH : HEAD = 16) by reflexivity.
assert (Hsc : spZ regsC = spZ regs - 144) by (rewrite Csp; reflexivity).
(* memC is mem outside the prologue's frame *)
assert (MC : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 144 \/ spZ regs <= a) ->
  memC (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hb. apply CM. rewrite wz by exact Ha. unfold FRAME_PSTR, FRAME_parse_string. lia. }
assert (SB : same_below mem memC alloc_ceiling) by (intros x Hx; apply MC; lia).
destruct HMP as [(Hcf & _) | (_ & res & HPOST)].
{ exfalso. unfold SIZE_MAXZ in Hfail. lia. }
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (Q10 & Q4096 & Qab & QFH & QRB & _ & QGL).
subst c'. rewrite C1r.
assert (HFP : forall a, inFP FS_PSTAT_FP a ->
  (inFP FS_PSTAT_FP a /\ exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly S) a \/ (inFP FS_PSTAT_FP a /\ in_img tfibsegs a)).
{ intros a Ha. right. right. split; [exact Ha | exact (pc_fp_img a Ha)]. }
destruct (fsw_rt_atU3 B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S U W
  memC mdC 0 STK_fuzz_malloc (spZ regsC) FS_PSTAT_FP [] ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md' 1
  CJ HJc OK' PO' ltac:(lia) ltac:(lia) HFP) as (HJ2 & HARU2).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J10 & _ & _ & _ & Hpres2 & _).
(* the bytes at or above the call's sp: kept by the callee (its window lies below), memC = mem above spZ regs *)
assert (KEEPS : forall a, spZ regs - 144 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) memC a).
{ intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md' a HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W memC mdC a CARU) by lia.
  apply F1; lia. }
assert (KEEPA : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. rewrite KEEPS by lia. apply (aview_at tfibsegs). apply MC; lia. }
(* the text block's bytes: an old live block, outside FP, kept by the composed journal's live-block clause *)
assert (KEEPT : forall x, text - HEAD <= x < text + tcap ->
  aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x).
{ intros x Hx.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR HTX1)
    as (_ & _ & Hbc & Happ & _).
  rewrite ps2_req in Hbc, Happ by lia.
  assert (Hxa : app_addr x) by (apply (in_app_addr _ _ x Happ); lia).
  assert (UN : forall U0 ly0 S0 (W0 : world tfibsegs) mem0 md0, ARU tfibsegs B ly0 S0 U0 W0 mem0 md0 ->
     aview tfibsegs (w_H W0) (unpoison U0 mem0) x = aview tfibsegs (w_H W0) mem0 x).
  { intros U0 ly0 S0 W0 mem0 md0 HA. apply (aview_at tfibsegs). apply unpoison_out.
    unfold app_addr, ASAN_CEIL in Hxa. rewrite wz by lia.
    destruct (in_ush U0 x) eqn:E; [exfalso|reflexivity].
    pose proof (ush_facts tfibsegs B ly0 S0 U0 W0 mem0 md0 x HA E) as (_ & L1 & L2).
    unfold kLowShadowBeg, SHADOW_OFF in *. lia. }
  rewrite <- (UN _ _ _ _ _ _ HARU2), <- (UN _ _ _ _ _ _ HARU0).
  replace x with (text - HEAD + (x - (text - HEAD))) by lia.
  apply (J10 (text - HEAD) (tcap + HEAD) (x - (text - HEAD)));
    [exact HTX1 | rewrite Qab; apply in_or_app; left; exact HTX1 | rewrite ps2_req by lia; lia |].
  intros Hf. apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD)
    (text - HEAD + (x - (text - HEAD))) HAR HTX1); [rewrite ps2_req by lia; lia | exact (pc_fp_img _ Hf)]. }
(* the stack window [spZ regs - STK_parse_string, ot) is present after the call *)
assert (WRn : forall a, spZ regs - STK_parse_string <= a < ot -> writable_at tfibsegs (mrestrict (w_H W') mem') a).
{ intros a Ha. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md' a HARU2); [lia|].
  apply Hpres2. lia. }
assert (Hrb : fs_rblock tfibsegs B ly' S' W' mem' res (Q + 1)) by (apply QRB; lia).
assert (PR : forall r : Z, acallee_saved r -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regsC (Z_to_bv 5 r))
  by exact HP.
apply (HK ly' S' W' regs' mem' md' res).
unfold pstr_ret_facts.
split.
{ transitivity (spZ regsC); [unfold spZ; exact (f_equal bv_unsigned (PR 2 ltac:(unfold acallee_saved; lia)))|exact Csp]. }
split; [exact Q10|].
split; [rewrite <- C3r; exact (PR 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C4r; exact (PR 4 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C8; exact (PR 8 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C9; exact (PR 9 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C20; exact (PR 20 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C22; exact (PR 22 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C23; exact (PR 23 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C24; exact (PR 24 ltac:(unfold acallee_saved; lia))|].
split.
{ (* the 13 frame words, in [spZ regsC + 0x28, spZ regsC + 0x90) *)
  unfold pstr_frame_at in *. apply Forall_forall. intros c Hc.
  pose proof (proj1 (Forall_forall _ _) CF c Hc) as Hv. cbn beta in Hv |- *.
  assert (Hoff : 40 <= fst c /\ fst c + 8 <= 144).
  { unfold pstr_saved in Hc. repeat (destruct Hc as [<- | Hc]; [cbn [fst]; lia|]). destruct Hc. }
  apply (val_mem_kept tfibsegs (w_H W) (w_H W') memC mem' _ 8 _); [|exact Hv].
  intros k Hk. unfold FRAME_PSTR, FRAME_parse_string in *. apply KEEPS. lia. }
split; [exact HJ2|].
split; [exact HARU2|].
split; [exact QFH|].
split; [exact Q4096|].
split; [exact (proj1 (proj2 Hrb))|].
split; [exact Qab|].
split; [exact Hrb|].
split.
{ apply (pc_pj_in_ok_keep (mrestrict (w_H W) mem)); [exact HIN | | |].
  - intros i Hi. apply (mbyte_of_aview tfibsegs). apply KEEPA.
    pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq1 & _). lia.
  - intros i Hi. apply WRn. lia.
  - intros i Hi. apply (mbyte_of_aview tfibsegs). apply KEEPT. lia. }
split.
{ split; [exact Htx1|]. split; [|exact Hlen].
  split; [rewrite Qab; apply in_or_app; left; exact HTX1|]. split; [exact Htx16|]. split; [exact Htc|].
  apply (val_mem_kept tfibsegs (w_H W) (w_H W') mem mem' _ 8 _); [|exact Htxv].
  intros k Hk. apply KEEPT. lia. }
split.
{ intros a Ha _. split; [apply (mbyte_of_aview tfibsegs); apply KEEPA; lia|].
  split; intros _; [apply WRn; lia | apply (apresent_writable tfibsegs); apply Hotpres; lia]. }
rewrite Z.add_assoc in QGL. exact QGL.
Qed.
End W3.

(* ================= the composition: stage 1, the fuzz_malloc call 0x85614, stage 2 =================
   parse_string_proof : fuzz_malloc_spec tfibsegs B -> parse_string_spec tfibsegs B, on the CTX-drop statements
   (a working branch faa7e2570e5: neither spec takes a CTX list). The call is SRr_bind over
   fuzz_malloc_spec at n = Q + 1, between pstr_call_pre (its premises at the call) and pstr_call_post (its post to
   stage 2's return-site facts); stage 2 is lib/B/FSW_parse_string_s2.v's pstr_stage2. *)
Section W4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

Theorem parse_string_proof : fuzz_malloc_spec tfibsegs B -> parse_string_spec tfibsegs B.
Proof.
intros MALLOC. unfold parse_string_spec.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail HPRE FH [chq HCH] Hq16 H10 HIN HWIN
  HTX Hp Hq Hrun HGL Hquiet HQm Hlive Hnev Hbb.
apply (pstr_stage1 B HSS ly S U W regs mem md ch q ot text len p d tb tcap Q _ HPRE FH H10 HIN HWIN HTX Hp Hq Hrun).
intros regsC memC mdC HCF.
destruct (pstr_call_pre B ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC chq
  HPRE HCH Hq16 HIN HWIN HTX Hrun HGL Hquiet HCF) as (HPREc & Era & HGLc).
pose proof Hrun as (HQ0 & _).
assert (C10 : YK11.getr regsC 10 = w64 (Q + 1)) by (destruct HCF as (_ & _ & C10 & _); exact C10).
eapply SRr_bind.
{ exact (MALLOC ly S U W regsC memC mdC chq (Q + 1) live peak cnt fail HPREc FH C10 ltac:(lia) HQm HGLc
    ltac:(lia) ltac:(pose proof Hquiet as (_ & _ & Hc); lia) ltac:(unfold EV_fuzz_malloc in Hnev; exact Hnev) (fun _ => Hbb)). }
intros W' c' _ HMP.
apply (pstr_call_post B ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC _ W' c'
  HPRE HIN HWIN HTX Hrun HGL Hquiet HCF); [|exact HMP].
intros ly2 S2 W2 regs2 mem2 md2 a HRF.
eapply SRr_mono.
{ exact (pstr_stage2 B (proj1 HSS) (proj2 HSS) ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail
    ly2 S2 W2 regs2 mem2 md2 a HPRE FH H10 HIN HWIN HTX Hp Hq Hrun HGL Hquiet HQm Hlive HRF). }
intros W'' c'' _ HPOST. exists a. exact HPOST.
Qed.
End W4.
