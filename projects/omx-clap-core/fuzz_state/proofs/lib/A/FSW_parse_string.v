(* fs program part, READER group: the ASan walk of parse_string (A_parse_string 0x850b8, pf.c:117-181) over fs.asan,
   PLAIN-BYTE CASE: two stages, the fuzz_malloc call step, and their composition.
   rule 24: no released ASan proof of parse_string (r24-confirm-all.md, index v5 2026-10-28T21:58:24Z). The released
   hits for the name parse_string are the PLAIN-image proofs lib/Prog/parse_string.v / parse_string_c.v (and their CF /
   U twins, and fuzz_preset's copies of the same source function), which this walk uses only as the control-flow
   template.

   THE SHAPE. parse_string runs at FP = FS_PSTAT_FP and calls fuzz_malloc, which also runs at FP = FS_PSTAT_FP; the
   journals compose over RELOC's FP-keyed core (a working branch 4aa3d96b823: ajournal's image clause
   exempts `inFP FP a`, so alloc.c's statics may change under the FP; on S0's own core they are frozen and the
   callee's post cannot hold). So:
     stage 1  pstr_stage1      entry 0x850b8 -> the fuzz_malloc call 0x85180 (the escape-free scan loop), in
                               continuation form: it consumes a continuation at the callee's entry 0x828ac under
                               pstr_call_facts and gives SRr at the entry.
     call     pstr_call_step   the call: the callee's fpreU (FSW_ret.v fsw_fpreU_atFP), fuzz_malloc_spec
                               at n = Q + 1 (`1 <= Q + 1` proved from plain_run's 0 <= Q), and the journal
                               composition (FSW_K3.v), giving pstr_ret_facts at the return 0x85184.
     stage 2  pstr_stage2      the return 0x85184 -> the `ret` 0x855fc (the copy loop, the NUL, the in->p store, the
                               epilogue), concluding parse_string_spec's fpostU through FSW_ret.v's fsw_retU.
   THE COMPOSITION parse_string_proof : fuzz_malloc_spec tfibsegs B -> parse_string_spec tfibsegs B (FSH_Fn_reader.v,
   S0 CTX-drop form, a working branch faa7e2570e5). It replaces the interim parse_string_proof_c5, which
   carried a per-instance `In (RA_PSTR_MALLOC :: spine chq) CTXm` premise only to discharge fuzz_malloc_spec's old
   In-CTX clause; the owner dropped that clause and its CTX binder from the allocator, writer and reader specs
   (a Theorem Labs lane 2026-10-29T05:00-05:05Z), so neither the premise nor a CTX list appears here. No Admitted, no Axiom,
   no Parameter, no admit, no timeout.

   THE CODE (capstone over the unstripped twin, same loadable bytes as the pinned fs.asan; listing
   a Theorem Labs lane's parse_string.A.s, 389 four-byte instructions 0x850b8 .. 0x856c8): prologue and the shadow base
   through the GOT (0x850f0 `auipc a1,0x1a` + 0x850f4 `ld a1,0x600(a1)` reads 0x9f6f0, the GOT word of
   __asan_shadow_memory_dynamic_address - the address FSW_K's fsw_entryT_args names), the two 8-byte shadow checks of
   in->p / in->end, the escape-free scan loop 0x8513c..0x85168, the call `jal fuzz_malloc` 0x85180 (return 0x85184),
   the copy loop 0x85200..0x85424, the NUL store 0x85610, the in->p store 0x85620 and the epilogue 0x855c0..0x855fc.
   On the plain-byte path hex4 (0x85494), put_utf8 (0x854cc) and fuzz_free (0x855b8) are not reached and no
   __asan_report_* branch is taken.

   PORT-FROM / SOURCES (searched with git grep over origin/main and this worktree, lane rule 22:0xZ):
   - the walk kit lib/A/FSW_K.v: fss0T_args / fsw_entryT_args
     (entry with the shadow base), fsw_ajournal_init_ot (the raised window top ot), fsw_aj_run_tokU /
     fsw_aj_run_to_tokU (U-form token runs), fs_Bx / fs_Bspan, fsw_field, fsw_reg_*, fsw_region_nth, fsw_preserved,
     fsw_apresent_unpoison; lib/A/FSW_ret.v (a Theorem Labs lane, in the same kit head): fsw_retU, the U-form return;
     lib/A/FSW_K3.v: fsw_rt_atU3, the journal composition at a
     program call under a non-empty caller FP.
   - the decode table lib/A/FSW_parse_string_tbl.v (this lane).
   - the stack's shadow-zero range (pstr_RA_stack below) is lib/A/ACex.v:322-339 (stack_cells8 / RA_stack) restated,
     and pstr_shx is lib/A/ACep.v:203-213 (denot_shx) restated: ACex.v and ACep.v cannot be imported on this head
     (they Require A/ACej.v, which still carries RELOC's refusal marker port_core_refused_80878 at ACej.v:30, and
     A/AD25.v's file AD2i.v fails to compile too).
   - the block arm is Reusable/YCbq.v:2686 range_addressable_of_block (imported, not restated).
   - the stack's shadow under unpoison U is lib/A/FSupoisonStack.v's fsw_ARU_stack_ra (a working branch
     52f226102ef, a Theorem Labs lane's kit item; it replaced this file's own pstr_ush_stk). No existing lemma was found for the
     block case (pstr_ush_blk: no head of U covers a live block's user byte): FSupoisonU / FSupoisonStack have none on
     this head, and ALLOC's lib/A/FSW_strkit.v (a working branch 8a3773fd93f) has only the converse
     direction ush_off_addressable; that branch is not merged here.
   - stage 2's helpers (Section W2, prefix ps2_), searched before writing: `req_size n = n` has a hit only in another
     unit (tcpreplay A1AinvW.v:52), so ps2_req; `frame_of E rs m m' ->` is empty (YI04.frame_of_ro covers read-only
     regions only; YN0i.wsub cannot be imported: it declares `Notation B`), so ps2_frame_wins; the pointwise
     mbyte / bytes_at transports and the `Ereg` value readers (ps2_ewR / ps2_ewX over YI04's ew_Ereg_nat /
     ew_Ereg_extra) have no hit; `in_img tfibsegs` has none (FSW_K's fs_segs_img is the converse), so ps2_img_hi. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_K3 FSW_parse_string_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the addresses of the walk (FSH_Base.A_parse_string and the listing) ---- *)
Definition RA_PSTR_MALLOC : Z := 0x85184.      (* after `jal fuzz_malloc` 0x85180 *)
Definition PSTR_SCAN : Z := 0x8513c.           (* the scan loop head *)
Definition PSTR_RET : Z := 0x855fc.            (* the `ret` *)
(* the prologue's frame, 0x90: FSH_Base names it, this file never restates the numeral *)
Definition FRAME_PSTR : Z := FRAME_parse_string.
(* the 13 callee-saved words the prologue writes, as (offset in the frame, register number): ra at 0x88 down to
   s11 at 0x28 (listing 0x850bc .. 0x850ec) *)
Definition pstr_saved : list (Z * Z) :=
  [(0x88, 1); (0x80, 8); (0x78, 9); (0x70, 18); (0x68, 19); (0x60, 20); (0x58, 21); (0x50, 22); (0x48, 23);
   (0x40, 24); (0x38, 25); (0x30, 26); (0x28, 27)].

(* concrete bounds the symbolic engine's range reasoning uses: the caller's struct pj_in is on the real stack
   ([2 ^ 46, 2 ^ 47]), the text block is application memory below alloc_ceiling (asan_consts) *)
Definition RQLO : Z := 2 ^ 46.
Definition RQHI : Z := 2 ^ 47 - 24.
Definition RTLO : Z := 4096.
Definition RTHI : Z := 0x7fffff800000.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair FSW_K's entry states need (FSH_Base.v: the GOT word 0x9f6f0 and the cell 0xa7f38 of
   __asan_shadow_memory_dynamic_address). It is the donor TfibLib's tl_got_shadow / tl_shadow_cell, which
   lib/A/ACeg.v would discharge once its ACej.v dependency loses RELOC's refusal marker. *)
Hypothesis HSS : FsShadowSyms B.
Let TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

(* ---- the two interfaces the stages meet at: the state at the fuzz_malloc call (stage 1's conclusion, in the form
   FSW_K's call steps consume: fsw_after_callU / FSW_ret's fsw_after_callU_args take exactly the caller journal, the
   ARU, the resumed sp and the frame chunks) and the state at its return (stage 2's premise, what that call step and
   FSH_Fn_alloc.fuzz_malloc_spec give back) ---- *)
Definition pstr_frame_at (W : world tfibsegs) (mem : word -> option byte) (regs0 : bvmap 5 word) (sp : Z) : Prop :=
  Forall (fun c => val_mem tfibsegs (mrestrict (w_H W) mem) (sp + fst c) 8
                     (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (snd c))))) pstr_saved.
Definition pstr_call_facts (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ot q p Q : Z)
  (regsC : bvmap 5 word) (memC : word -> option byte) (mdC : Model) : Prop :=
  spZ regsC = spZ regs - FRAME_PSTR /\
  YK11.getr regsC 1 = w64 RA_PSTR_MALLOC /\ YK11.getr regsC 10 = w64 (Q + 1) /\
  YK11.getr regsC 3 = YK11.getr regs 3 /\ YK11.getr regsC 4 = YK11.getr regs 4 /\
  YK11.getr regsC 8 = w64 q /\ YK11.getr regsC 9 = w64 (q + 8) /\ YK11.getr regsC 20 = w64 (p + 1) /\
  YK11.getr regsC 23 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regsC 24 = w64 SHADOW_OFF /\
  YK11.getr regsC 25 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  (forall x : word, ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) -> memC x = mem x) /\
  pstr_frame_at W memC regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U memC) mdC 0 /\
  ARU tfibsegs B ly S U W memC mdC.
(* at the return 0x85184: fuzz_malloc's block (a - HEAD, Q + 1 + HEAD) is live and its head is the appended U entry,
   the caller's frame and the caller's data are untouched, and the journal of the entry carries one tick *)
Definition pstr_ret_facts (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ot q p d Q text len tcap live peak cnt fail a : Z) (tb : list byte)
  (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  (md2 : Model) : Prop :=
  spZ regs2 = spZ regs - FRAME_PSTR /\
  YK11.getr regs2 10 = w64 a /\
  YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 q /\ YK11.getr regs2 9 = w64 (q + 8) /\ YK11.getr regs2 20 = w64 (p + 1) /\
  YK11.getr regs2 23 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regs2 24 = w64 SHADOW_OFF /\
  YK11.getr regs2 25 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  pstr_frame_at W2 mem2 regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 EV_fuzz_malloc /\
  ARU tfibsegs B ly2 S2 (U ++ [(a - HEAD, HEAD)]) W2 mem2 md2 /\
  FSupoisonU.fs_heads B ly2 S2 (U ++ [(a - HEAD, HEAD)]) /\
  4096 + HEAD <= a /\ a mod 16 = 0 /\
  ablocks B ly2 S2 = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
  fs_rblock tfibsegs B ly2 S2 W2 mem2 a (Q + 1) /\
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len p d tb /\
  rd_text tfibsegs B ly2 S2 W2 mem2 text len tcap /\
  wkeep tfibsegs W W2 mem mem2 (spZ regs) ot q 24 /\
  fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail.
(* ---- the stack's shadow reads 0 (ACex.v:322-339, restated: see the header) ---- *)
Lemma pstr_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8)
    by lia. apply Z_mod_mult.
Qed.
Lemma pstr_RA_stack : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity))
  as Hz. cbn [fst snd] in Hz.
destruct (pstr_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.

(* ---- no shadow byte of a live block's user bytes is user-poisoned (the stack's case is FSupoisonStack's
   fsw_ARU_stack_ra) ---- *)
(* a live block's bytes from its 16-byte head on: no head of U covers their granules (every head is 8-aligned and
   16 long, and the blocks are pairwise disjoint) *)
Lemma pstr_ush_blk : forall ly S U (W : world tfibsegs) mem md b n x,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, n) (ablocks B ly S) -> b + 16 <= x -> x < b + req_size n -> in_ush U (SHADOW_OFF + x / 8) = false.
Proof.
intros ly S U W mem md b n x HARU FH Hin Hx1 Hx2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof HARU as (HAR & (OK & _) & _).
destruct (in_ush U (SHADOW_OFF + x / 8)) eqn:E; [exfalso | reflexivity].
apply in_ush_spec in E as (r & Hr & Hlo & Hhi).
pose proof (proj1 (Forall_forall _ _) OK r Hr) as (Hal & _ & _ & _).
destruct (FH r Hr) as (Hsnd & m & Hinm & Hm16).
rewrite Hsnd in Hhi. unfold shadow_addr in Hlo, Hhi.
change (16 / 8) with 2 in Hhi.
assert (H16 : (fst r + 16) / 8 = fst r / 8 + 2)
  by (rewrite (Z.div_mod (fst r) 8 ltac:(lia)) at 1; rewrite Hal, Z.add_0_r;
      replace (8 * (fst r / 8) + 16) with (16 + (fst r / 8) * 8) by lia; rewrite Z.div_add by lia; lia).
destruct (Z.eq_dec (fst r) b) as [Heq | Hne].
- assert (Hge : (fst r + 16) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
- pose proof (req_size_pos m ltac:(destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (fst r) m HAR Hinm)
    as (_ & _ & _ & _ & _ & _ & Hm); lia)) as (_ & Hmle).
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m b n HAR Hinm Hin
    ltac:(intros Hq; apply Hne; exact (f_equal fst Hq))) as Hdis.
  unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
  destruct Hdis as [Hd | Hd].
  + assert (Hge : (fst r + 16) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
  + assert (Hlt : x / 8 < fst r / 8).
    { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as D.
      rewrite Hal, Z.add_0_r in D. lia. }
    lia.
Qed.
(* the shadow byte of an address no head covers reads the same on the machine's memory and on its unpoisoned
   reading, so a range addressable there is addressable here *)
Lemma pstr_RA_unp : forall U (W : world tfibsegs) mem x n,
  0 <= x -> x + n < 2 ^ 64 ->
  (forall a, x <= a < x + n -> in_ush U (SHADOW_OFF + a / 8) = false) ->
  range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF x n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros U W mem x n Hx Hn Hush HRA.
apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W) mem)
  SHADOW_OFF x n); [|exact HRA].
intros a Ha. unfold shadow_of_addr. symmetry. apply aview_unpoison_out.
rewrite (wz (SHADOW_OFF + a / 8)); [apply Hush; exact Ha|].
pose proof (Z.div_pos a 8 ltac:(lia)). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold SHADOW_OFF. lia.
Qed.
(* the two ranges the walk reads and writes, over the MACHINE's memory: the caller's struct pj_in on the real
   stack, and the user bytes of a live reader block (the text, and later the new block) *)
Lemma pstr_RA_stk_mem : forall ly S U (W : world tfibsegs) mem md x n,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= ly_stk_lo ly -> ly_stk_hi ly <= 2 ^ 47 ->
  ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md x n HARU Hceil H47 Hlo Hhi Hx8 Hn8 Hn.
pose proof HARU as (HAR & _ & _).
apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) ly S U W mem md (w_H W) x n HARU Hlo
  ltac:(lia))).
exact (pstr_RA_stack ly S W (unpoison U mem) md x n HAR Hlo Hhi Hx8 Hn8 Hn).
Qed.
Lemma pstr_RA_blk_mem : forall ly S U (W : world tfibsegs) mem md b k x n,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, k) (ablocks B ly S) -> b + 16 <= x -> 0 <= n -> x + n <= b + req_size k ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md b k x n HARU FH Hin Hx1 Hn0 Hx2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof HARU as (HAR & _ & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b k HAR Hin) as (_ & Hb4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
destruct (Z.le_gt_cases n 0) as [Hle | Hgt]; [apply range_addressable_nil; lia|].
apply (pstr_RA_unp U W mem x n ltac:(lia) ltac:(lia)).
- intros a Ha. exact (pstr_ush_blk ly S U W mem md b k a HARU FH Hin ltac:(lia) ltac:(lia)).
- exact (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md b k x n HAR Hin ltac:(lia)
    ltac:(lia)).
Qed.
(* ---- arithmetic of the scan loop's seqz (pf.c:123: the cursor advances by 2 at a backslash, else by 1): for a
   byte that is not a backslash the test is 0, so the cursor advances by one ---- *)
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

(* ---- the two values the loop body computes: the cursor after a plain byte, and the length a0 = Q + 1 at the
   fuzz_malloc call ---- *)
Lemma pstr_loop_cond_val : forall E c x, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 -> c <> 92 ->
  ew E 10 = Z_to_bv 64 x -> 0 <= x -> x + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SOff 10 0)) (SLit 1)) = x + 1.
Proof.
intros E c x H32 Hc Hne H10 Hx0 Hx1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (pstr_sltu_not92 E c Hc Hne H32), (U_atom E 10 x H10 ltac:(lia)), U_SLit.
rewrite (zcanon_id 1) by (unfold M64; lia). rewrite Z.add_0_l.
rewrite (zcanon_id x) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
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

(* ---- the scan loop's head state (0x8513c): every register an atom, a2 pinned to the quote literal, the text byte
   at the cursor a0 as a 1-byte region with the byte as atom 32, and the shadow base in s8 (atom 24) as the token
   run's Bx ---- *)
Definition pstr_BxL : sv := SOff 24 0.
Definition pstr_regsL : list sv := sr_set sr_atoms 12%bv (SLit 34).
Definition pstr_regionL : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition pstr_factsL : facts := mkFacts
  [(10%nat, mkAF RTLO RTHI 0); (11%nat, mkAF RTLO RTHI 0); (20%nat, mkAF RTLO RTHI 0);
   (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 32 255 0)] [] [].
Definition pstr_ssL : sstate := mkSS PSTR_SCAN pstr_regsL [pstr_regionL] None pstr_factsL.

Lemma pstr_ssL_ok : forall (W : world tfibsegs) regs1 mem1 x c tl pp1,
  YK11.getr regs1 10 = w64 x -> YK11.getr regs1 11 = w64 tl -> YK11.getr regs1 12 = w64 34 ->
  YK11.getr regs1 20 = w64 pp1 -> YK11.getr regs1 24 = w64 SHADOW_OFF ->
  RTLO <= x <= RTHI -> RTLO <= tl <= RTHI -> RTLO <= pp1 <= RTHI ->
  32 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) x 1 c ->
  st_ok tfibsegs (Ereg regs1 [w64 c]) pstr_ssL
    (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 PSTR_SCAN) mem1 (YK11.seg_rom tfibsegs))).
Proof.
intros W regs1 mem1 x c tl pp1 H10 H11 H12 H20 H24 Hx Htl Hpp Hc Hval.
assert (E10 : bv_unsigned (ew (Ereg regs1 [w64 c]) 10) = x)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl), H10; apply wz; unfold RTLO, RTHI in *; lia).
assert (E11 : bv_unsigned (ew (Ereg regs1 [w64 c]) 11) = tl)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 11 11%bv eq_refl), H11; apply wz; unfold RTLO, RTHI in *; lia).
assert (E20 : bv_unsigned (ew (Ereg regs1 [w64 c]) 20) = pp1)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 20 20%bv eq_refl), H20; apply wz; unfold RTLO, RTHI in *; lia).
assert (E24 : bv_unsigned (ew (Ereg regs1 [w64 c]) 24) = SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs1 [w64 c] 24 24%bv eq_refl), H24; apply wz; unfold SHADOW_OFF; lia).
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
  rewrite E10, E11, E20, E24, U32.
  rewrite !Z.pow_0_r.
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I].
Qed.

(* ---- the bytes of the text, as the walk reads them ---- *)
Lemma pstr_mrd_mbyte : forall (m : word -> option byte) a, Mem.mrd tfibsegs m (Mem.wa a) = mbyte tfibsegs m a.
Proof. intros m a. reflexivity. Qed.
Lemma pstr_val1 : forall (m : word -> option byte) a (cb : byte),
  mbyte tfibsegs m a = Some cb -> val_mem tfibsegs m a 1 (bv_unsigned cb).
Proof.
intros m a cb H k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, H. f_equal.
pose proof (bv_unsigned_in_range 8 cb) as Hr. change (bv_modulus 8) with 256 in Hr.
replace (YO0f.le_byte (bv_unsigned cb) 1 0) with (bv_unsigned cb);
  [symmetry; apply Z_to_bv_bv_unsigned|].
unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
replace (8 * Z.of_nat 1) with 8 by lia. change (2 ^ 8) with 256.
rewrite (Z.mod_small (bv_unsigned cb) 256) by lia. rewrite (Z.mod_small (bv_unsigned cb) 256) by lia. reflexivity.
Qed.
Lemma pstr_text_byte : forall (W : world tfibsegs) m q text len p d (tb : list byte) k (cb : byte),
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) m) q text len p d tb ->
  nth_error tb (Z.to_nat k) = Some cb -> 0 <= k ->
  mbyte tfibsegs (mrestrict (w_H W) m) (text + k) = Some cb.
Proof.
intros W m q text len p d tb k cb HIN Hnth Hk.
assert (Hlt : (Z.to_nat k < length tb)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbt & _).
destruct Hbt as (_ & _ & Hb). specialize (Hb (Z.to_nat k) Hlt).
rewrite Z2Nat.id in Hb by exact Hk. rewrite Hnth in Hb. exact Hb.
Qed.
(* ---- a run whose only region has an empty write window leaves the memory alone ---- *)
Lemma pstr_frame_none : forall E (r : YP09.region) (m m' : word -> option byte),
  YP09.r_whi r <= YP09.r_wlo r -> frame_of E [r] m m' -> forall y, m' y = m y.
Proof.
intros E r m m' Hw HF y. apply HF. intros (r0 & [<-|[]] & Hr). lia.
Qed.
Lemma pstr_frame_none_l : forall E (rs : list YP09.region) (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall y, m' y = m y.
Proof.
intros E rs m m' Hw HF y. apply HF. intros (r0 & Hin & Hr).
rewrite Forall_forall in Hw. specialize (Hw r0 Hin). cbn beta in Hw. lia.
Qed.
Lemma pstr_mbyte_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall y, m' y = m y) -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H m m' a He. unfold mbyte, mrestrict. rewrite He. reflexivity. Qed.
Lemma pstr_val_mem_eq : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall y, m' y = m y) -> val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v He Hv k Hk. rewrite (pstr_mbyte_eq H m m' _ He). exact (Hv k Hk). Qed.
Lemma pstr_frame_at_eq : forall (W : world tfibsegs) (m m' : word -> option byte) regs0 sp,
  (forall y, m' y = m y) -> pstr_frame_at W m regs0 sp -> pstr_frame_at W m' regs0 sp.
Proof.
intros W m m' regs0 sp He HF. unfold pstr_frame_at in *.
apply Forall_forall. intros cc Hcc. exact (pstr_val_mem_eq _ m m' _ 8 _ He (proj1 (Forall_forall _ _) HF cc Hcc)).
Qed.

(* a register the run left as its own entry atom, read through the token runs' extended env *)
Lemma pstr_reg_keep : forall (H : word -> bool) E ss ms (r : bv 5) regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 33 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> (Z.to_nat (bv_unsigned r) < 33)%nat ->
  getr (ms_regs ms) r = getr regs0 r.
Proof.
intros H E ss ms r regs0 extra HS HAE Hsr Hlt.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hsr, fsw_SOff0, (proj1 HAE _ Hlt).
apply (ew_Ereg_nat regs0 extra _ r). pose proof (u5_range r). lia.
Qed.

Lemma pstr_val_mem_eq_at : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v He Hv k Hk. unfold mbyte, mrestrict. rewrite (He k Hk). exact (Hv k Hk).
Qed.

Tactic Notation "pstr_env" constr(HS) ident(nm) :=
  lazymatch type of HS with st_ok _ ?Ev _ _ => pose (nm := Ev) end.
Lemma pstr_byte_eq_dec : forall (E : env) c b, ew E 32 = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SLit 34)) = b -> (c =? 34) = b.
Proof.
intros E c b H32 Hb Hc. rewrite branch_eq_U, (U_atom E 32 c H32 Hb), (U_lit E 34 ltac:(lia)) in Hc. exact Hc.
Qed.

(* ---- the loop-head machine state of the escape-free scan (0x8513c), at the cursor x ---- *)
Definition pstr_loop_at (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ot q p text len x : Z)
  (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  YK11.getr regs1 10 = w64 x /\ YK11.getr regs1 11 = w64 (text + len) /\ YK11.getr regs1 12 = w64 34 /\
  YK11.getr regs1 20 = w64 (p + 1) /\
  YK11.getr regs1 8 = w64 q /\ YK11.getr regs1 9 = w64 (q + 8) /\
  YK11.getr regs1 23 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regs1 24 = w64 SHADOW_OFF /\
  YK11.getr regs1 25 = w64 (SHADOW_OFF + (q + 8) / 8) /\
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
  (forall regsC memC mdC, pstr_call_facts ly S U W regs mem md ot q p Q regsC memC mdC ->
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
destruct HL as (H10 & H11 & H12 & H20 & H8 & H9 & H23 & H24 & H25 & H3 & H4 & Hsp1 & Hmem1 & Hfr1 & HJ & HARU).
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
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v)) by (vm_compute; reflexivity).
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
pose proof (pstr_ssL_ok W regs1 mem1 x c (text + len) (p + 1) H10 H11 H12 H20 H24 HxRT HtlRT HppRT
  ltac:(lia) Hval) as HS.
assert (SHOK : sh_ok tfibsegs pstr_BxL (@nil shent) (Ereg regs1 [w64 c]) (mrestrict (w_H W) mem1))
  by apply Forall_nil.
unfold YG0d.cfg_at. change (w64 PSTR_SCAN) with (Z_to_bv 64 PSTR_SCAN).
assert (EU24 : YP0e.U (Ereg regs1 [w64 c]) pstr_BxL = SHADOW_OFF).
{ unfold pstr_BxL. apply (U_atom _ 24 SHADOW_OFF);
  [rewrite (ew_Ereg_nat regs1 [w64 c] 24 24%bv eq_refl); exact H24 | unfold SHADOW_OFF; lia]. }
assert (EU10 : YP0e.U (Ereg regs1 [w64 c]) (SOff 10 0) = x).
{ apply (U_atom _ 10 x); [rewrite (ew_Ereg_nat regs1 [w64 c] 10 10%bv eq_refl); exact H10 | lia]. }
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ rewrite EU24, EU10. cbn [ms_mem mkst].
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  refine (pstr_RA_blk_mem ly S U W mem1 md1 (text - HEAD) (tcap + HEAD) x 1 HARU FH Hin _ _ _);
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
  assert (R23 : getr (ms_regs ms0) 23 = getr regs1 23)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 23%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R24 : getr (ms_regs ms0) 24 = getr regs1 24)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 24%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  assert (R25 : getr (ms_regs ms0) 25 = getr regs1 25)
    by (apply (pstr_reg_keep (w_H W) Eqb _ ms0 25%bv regs1 [w64 c] HS HAE2); [vm_compute; reflexivity | vm_compute; lia]).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eqb _ ms0 HS ltac:(vm_compute; reflexivity)) as Hms0.
  cbn [ss_pc] in Hms0. rewrite Hms0.
  apply (HK (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md1) mat0 md1)).
  unfold pstr_call_facts.
  split; [unfold spZ; rewrite R2; exact Hsp1|].
  split; [exact R1|]. split; [exact R10|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|].
  split; [rewrite R8; exact H8|]. split; [rewrite R9; exact H9|].
  split; [rewrite R20; exact H20|]. split; [rewrite R23; exact H23|].
  split; [rewrite R24; exact H24|]. split; [rewrite R25; exact H25|].
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
  (* 0x85150 -> the loop's back branch at 0x85164 *)
  fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
  2:{ (* the cursor is still below in->end, so this arm is impossible *)
      exfalso. fold Epa in Hc0. revert Hc0. rewrite branch_ltu_U.
      rewrite (pstr_loop_cond_val Epa c x A32 ltac:(lia) Hc92' A10 ltac:(lia)
        ltac:(unfold RTLO, RTHI in HxRT; lia)).
      rewrite (U_atom Epa 11 (text + len) A11 ltac:(unfold RTLO, RTHI in HtlRT; lia)).
      replace (x + 1 <? text + len) with true by (symmetry; apply Z.ltb_lt; lia). discriminate. }
  (* 0x85164 -> the loop head 0x8513c, with the cursor one byte on *)
  fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan PSTR_SCAN.
  { cbn [add_cond ss_mem]. unfold pstr_ssL. cbn [ss_mem].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (Hmemeq : forall y, ms_mem ms1 y = mem1 y).
  { intros y. rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF1 y).
    rewrite (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF0 y).
    exact (pstr_frame_none _ pstr_regionL _ _ ltac:(unfold pstr_regionL; cbn; lia) HF y). }
  assert (N10 : getr (ms_regs ms1) 10 = w64 (x + 1)).
  { lazymatch type of HS with st_ok _ _ ?SS _ =>
      assert (Hsr10 : sr_get (ss_regs SS) 10%bv
        = SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SOff 10 0)) (SLit 1))
        by (vm_compute; reflexivity) end.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) Epa _ ms1 10%bv HS), Hsr10, denot_lit_U.
    rewrite (pstr_loop_cond_val Epa c x A32 ltac:(lia) Hc92' A10 ltac:(lia)
      ltac:(unfold RTLO, RTHI in HxRT; lia)). reflexivity. }
  assert (N12 : getr (ms_regs ms1) 12 = w64 34)
    by (eapply fsw_reg_lit; [exact HS | vm_compute; reflexivity | lia]).
  assert (N2 : getr (ms_regs ms1) 2 = getr regs1 2)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 2%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N3 : getr (ms_regs ms1) 3 = getr regs1 3)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 3%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N4 : getr (ms_regs ms1) 4 = getr regs1 4)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 4%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N8 : getr (ms_regs ms1) 8 = getr regs1 8)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 8%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N9 : getr (ms_regs ms1) 9 = getr regs1 9)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 9%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N11 : getr (ms_regs ms1) 11 = getr regs1 11)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 11%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N20 : getr (ms_regs ms1) 20 = getr regs1 20)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 20%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N23 : getr (ms_regs ms1) 23 = getr regs1 23)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 23%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N24 : getr (ms_regs ms1) 24 = getr regs1 24)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 24%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  assert (N25 : getr (ms_regs ms1) 25 = getr regs1 25)
    by (apply (pstr_reg_keep (w_H W) Epa _ ms1 25%bv regs1 [w64 c] HS HAE); [vm_compute; reflexivity | vm_compute; lia]).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Epa _ ms1 HS ltac:(vm_compute; reflexivity)) as Hms1.
  cbn [ss_pc] in Hms1. rewrite Hms1.
  refine (IH (Z.to_nat (Q - (i + 1))) ltac:(lia) (i + 1) (ms_regs ms1) (ms_mem ms1) _ ltac:(lia) _ eq_refl).
  unfold pstr_loop_at.
  split; [replace (p + 1 + (i + 1)) with (x + 1) by lia; exact N10|].
  split; [rewrite N11; exact H11|]. split; [exact N12|].
  split; [rewrite N20; exact H20|].
  split; [rewrite N8; exact H8|]. split; [rewrite N9; exact H9|].
  split; [rewrite N23; exact H23|]. split; [rewrite N24; exact H24|].
  split; [rewrite N25; exact H25|].
  split; [rewrite N3; exact H3|]. split; [rewrite N4; exact H4|].
  split; [unfold spZ; rewrite N2; exact Hsp1|].
  split; [intros y Hy; rewrite (Hmemeq y); exact (Hmem1 y Hy)|].
  split; [exact (pstr_frame_at_eq W mem1 (ms_mem ms1) regs _ Hmemeq Hfr1)|].
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

(* the shadow address of an object, as the code computes it (lib/A/ACep.v:203-213 denot_shx, restated: ACep.v
   cannot be imported here, it Requires A/ACej.v with RELOC's refusal marker) *)
Lemma pstr_shx : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn ltac:(lia) ltac:(lia)), (U_atom E m sb Hm ltac:(lia)), U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
rewrite (zcanon_id ((v + c) / 8 + sb)) by (unfold M64; lia). lia.
Qed.

(* ---- stage 1: the entry 0x850b8 -> the fuzz_malloc call 0x85180 ---- *)
Definition pstr_gf_q : list (nat * afact) := [(10%nat, mkAF RQLO RQHI 3)].
Definition pstr_reg_p : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition pstr_reg_e : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition pstr_facts1 : facts := mkFacts
  [(8%nat, mkAF RQLO RQHI 3); (9%nat, mkAF RQLO (RQHI + 8) 3); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF RTLO RTHI 0); (33%nat, mkAF RTLO RTHI 0)] [] [].
Definition pstr_ss1 : sstate := mkSS 0x85124 sr_atoms [pstr_reg_p; pstr_reg_e] None pstr_facts1.

Lemma pstr_stage1 : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q Qp,
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  (forall regsC memC mdC, pstr_call_facts ly S U W regs mem md ot q p Q regsC memC mdC ->
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
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v)) by (vm_compute; reflexivity).
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
fsw_aj_run_tokU parse_string_tbl_ok HSE HJ HARU SHOK fs_Bspan.
{ rewrite EB32, (EB10 8 ltac:(lia)). cbn [ms_mem mkst].
  refine (pstr_RA_stk_mem ly S U W mem md (q + 8) 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _
    ltac:(reflexivity) ltac:(lia)).
  rewrite Zplus_mod, Bqal. reflexivity. }
{ rewrite EB32, (EB10 0 ltac:(lia)). cbn [ms_mem mkst]. rewrite Z.add_0_r.
  exact (pstr_RA_stk_mem ly S U W mem md q 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bqal
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
(* the machine state at 0x85124 *)
assert (M8 : getr (ms_regs ms) 8 = w64 q).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 8%bv = SOff 10 0) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 8%bv HSE), Hsr, fsw_SOff0, Ee10. reflexivity. }
assert (M9 : getr (ms_regs ms) 9 = w64 (q + 8)).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 9%bv = SOff 10 8) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 9%bv HSE), Hsr, denot_lit_U,
    (U_atom_off Ee 10 q 8 Ee10 ltac:(lia) ltac:(lia)). reflexivity. }
assert (M24 : getr (ms_regs ms) 24 = w64 SHADOW_OFF).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 24%bv = SOff 32 0) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 24%bv HSE), Hsr, fsw_SOff0, Ee32. reflexivity. }
assert (M23 : getr (ms_regs ms) 23 = w64 (SHADOW_OFF + q / 8)).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 23%bv
      = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 23%bv HSE), Hsr,
    (pstr_shx Ee 10 32 0 q SHADOW_OFF Ee10 Ee32 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia)). rewrite Z.add_0_r. reflexivity. }
assert (M25 : getr (ms_regs ms) 25 = w64 (SHADOW_OFF + (q + 8) / 8)).
{ lazymatch type of HSE with st_ok _ _ ?SS _ =>
    assert (Hsr : sr_get (ss_regs SS) 25%bv
      = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) by (vm_compute; reflexivity) end.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) Ee _ ms 25%bv HSE), Hsr,
    (pstr_shx Ee 10 32 8 q SHADOW_OFF Ee10 Ee32 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia)). reflexivity. }
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
(* the reseat at 0x85124: struct pj_in's two fields as regions, every register its own atom *)
assert (HQRQ : RQLO <= q <= RQHI) by (unfold RQLO, RQHI; lia).
assert (HLRT : RTLO <= text + len <= RTHI).
{ pose proof (al_blocks _ _ LAWS ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR Hin)
    as (_ & _ & Hcl & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(lia)) as (_ & Hrq).
  unfold RTLO, RTHI. lia. }
assert (HPRT : RTLO <= p <= RTHI) by (unfold RTLO, RTHI in HLRT |- *; lia).
assert (HS1 : st_ok tfibsegs (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) pstr_ss1
  (restrict (w_H W) (YK11.mkst (ms_regs ms) (Z_to_bv 64 0x85124) (ms_mem ms) (YK11.seg_rom tfibsegs)))).
{ assert (G8 : bv_unsigned (ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 8) = q)
    by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl), M8; unfold w64; apply wz; lia).
  assert (G9 : bv_unsigned (ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 9) = q + 8)
    by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl), M9; unfold w64; apply wz; lia).
  assert (G24 : bv_unsigned (ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 24) = SHADOW_OFF)
    by (rewrite (ew_Ereg_nat (ms_regs ms) _ 24 24%bv eq_refl), M24; unfold w64; apply wz;
        unfold SHADOW_OFF; lia).
  assert (G32 : ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 32 = Z_to_bv 64 p)
    by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G33 : ew (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) 33 = Z_to_bv 64 (text + len))
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite restrict_mkst_fx. unfold pstr_ss1. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold pstr_reg_p, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite G8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 32 0) p);
        [rewrite fsw_SOff0, G32; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Vp].
    + unfold pstr_reg_e, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite G9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (q + 8) 0 8 (SOff 33 0) (text + len));
        [rewrite fsw_SOff0, G33; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Ve].
  - unfold pstr_reg_p, pstr_reg_e. cbn [pairwise_disjoint all_disjoint].
    split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite G8, G9. left. lia.
  - split; [|split; exact I]. unfold pstr_facts1. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite G8, G9, G24, G32, G33.
    rewrite (wz p ltac:(unfold RTLO, RTHI in HPRT; lia)),
      (wz (text + len) ltac:(unfold RTLO, RTHI in HLRT; lia)).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r.
    split; [split; [unfold RQLO, RQHI in *; lia | split; [exact Bqal | lia]]|].
    split; [split; [unfold RQLO, RQHI in *; lia | split; [rewrite Zplus_mod, Bqal; reflexivity | lia]]|].
    split; [split; [unfold SHADOW_OFF; lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I]. }
assert (SHOK1 : sh_ok tfibsegs pstr_BxL (@nil shent)
  (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) (mrestrict (w_H W) (ms_mem ms))) by apply Forall_nil.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Ee _ ms HSE ltac:(vm_compute; reflexivity)) as Hmsf.
cbn [ss_pc] in Hmsf. rewrite Hmsf.
clear SHOK HSE.
fsw_aj_run_tokU parse_string_tbl_ok HS1 HJ HARU SHOK1 fs_Bspan.
{ unfold pstr_ss1. cbn [ss_mem].
  apply awr_ok_cons_ro; [unfold pstr_reg_p; cbn; lia|].
  apply awr_ok_cons_ro; [unfold pstr_reg_e; cbn; lia | apply awr_ok_nil]. }
srr_branch_tok parse_string_tbl_ok HS1 SHOK1 fs_Bspan.
{ (* in->p + 1 is below in->end, so the failure exit is not taken *)
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
(* 0x85130 -> the scan loop head 0x8513c *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS1 HJ HARU SHOK1 fs_Bspan PSTR_SCAN.
{ cbn [add_cond ss_mem]. unfold pstr_ss1. cbn [ss_mem].
  apply awr_ok_cons_ro; [unfold pstr_reg_p; cbn; lia|].
  apply awr_ok_cons_ro; [unfold pstr_reg_e; cbn; lia | apply awr_ok_nil]. }
pstr_env HS1 Eh.
assert (HAEh : env_agree 34 (Ereg (ms_regs ms) [w64 p; w64 (text + len)]) Eh)
  by (unfold Eh; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]).
assert (H32h : ew Eh 32 = Z_to_bv 64 p)
  by (rewrite (proj1 HAEh 32%nat ltac:(lia)); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (H33h : ew Eh 33 = Z_to_bv 64 (text + len))
  by (rewrite (proj1 HAEh 33%nat ltac:(lia)); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
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
assert (L9 : getr (ms_regs ms1) 9 = getr (ms_regs ms) 9)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 9%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L23 : getr (ms_regs ms1) 23 = getr (ms_regs ms) 23)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 23%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L24 : getr (ms_regs ms1) 24 = getr (ms_regs ms) 24)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 24%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (L25 : getr (ms_regs ms1) 25 = getr (ms_regs ms) 25)
  by (apply (pstr_reg_keep (w_H W) Eh _ ms1 25%bv (ms_regs ms) [w64 p; w64 (text + len)] HS1
      ltac:(eapply env_agree_le; [|exact HAEh]; lia)); [vm_compute; reflexivity | vm_compute; lia]).
assert (Hwf2 : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [pstr_reg_p; pstr_reg_e])
  by (repeat (apply Forall_cons; [unfold pstr_reg_p, pstr_reg_e; cbn; lia|]); apply Forall_nil).
assert (Hmem2 : forall y, ms_mem ms1 y = ms_mem ms y).
{ intros y. rewrite (pstr_frame_none_l _ _ _ _ Hwf2 HF1 y). exact (pstr_frame_none_l _ _ _ _ Hwf2 HF0 y). }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eh _ ms1 HS1 ltac:(vm_compute; reflexivity)) as Hmsg.
cbn [ss_pc] in Hmsg. rewrite Hmsg.
refine (pstr_scan_loop ly S U W regs mem md q ot text len p tb tcap Q Qp FH HTX HPR Blen ltac:(lia)
  ltac:(lia) HTB ltac:(lia) HK 0 (ms_regs ms1) (ms_mem ms1) _ ltac:(lia) _).
unfold pstr_loop_at.
split; [replace (p + 1 + 0) with (p + 1) by lia; exact L10|].
split; [exact L11|]. split; [exact L12|]. split; [exact L20|].
split; [rewrite L8; exact M8|]. split; [rewrite L9; exact M9|].
split; [rewrite L23; exact M23|]. split; [rewrite L24; exact M24|]. split; [rewrite L25; exact M25|].
split; [rewrite L3; exact M3|]. split; [rewrite L4; exact M4|].
split; [unfold spZ; rewrite L2; exact M2|].
split; [intros y Hy; rewrite (Hmem2 y); exact (Hmem1 y Hy)|].
split; [exact (pstr_frame_at_eq W (ms_mem ms) (ms_mem ms1) regs _ Hmem2 Hfr1)|].
split; [exact HJ | exact HARU].
Qed.
End W.

(* ================= stage 2: the return of fuzz_malloc 0x85184 -> `ret` 0x855fc =================
   The copy loop 0x85200..0x85424, the NUL 0x85610, the in->p store 0x85620, the epilogue 0x855c0..0x855fc and the
   return itself (FSW_ret.v fsw_retU), concluding parse_string_spec's fpostU. Its premises are the spec's plus
   pstr_ret_facts: what the fuzz_malloc call step hands back. Its own section, so that the ps2_ names do not mix
   with stage 1's. *)
Section W2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.

(* ---- the walk's symbolic vocabulary: inside the body the shadow base is s8 (atom 24), and s7 / s9 hold the shadow
   cells of in->p / in->end as `(x >> 3) + s8`, the form the token engine reads (YCbn.v match_x) ---- *)
Definition ps2_Bq : sv := SOff 24 0.
Definition ps2_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 24 0).

(* ---- small helpers over the symbolic state and the machine's memory ---- *)
Lemma ps2_ewR : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64. apply unsigned_lit_small; exact Hv.
Qed.
Lemma ps2_ewX : forall regs extra (j : nat) v, nth j extra (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Ereg regs extra) (32 + j)) = v.
Proof. intros regs extra j v Hj Hv. rewrite ew_Ereg_extra, Hj. unfold w64. apply unsigned_lit_small; exact Hv. Qed.
Lemma ps2_shx_denot : forall E n x, bv_unsigned (ew E n) = x -> bv_unsigned (ew E 24) = SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> sv_denot E (ps2_shx n) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E n x Hn H24 Hx. unfold ps2_shx, w64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, H24, !Z.add_0_r.
replace (Z.land (zcanon 3) 63) with 3 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (x / 8)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia). rewrite Z.add_comm. apply zcanon_id.
unfold M64, SHADOW_OFF. lia.
Qed.
Lemma ps2_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w64 v ->
  YK11.getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. exact He. Qed.
Lemma ps2_denot_off : forall E n z v w, bv_unsigned (ew E n) = v -> w = v + z -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 w.
Proof.
intros E n z v w Hn Hw Hz. subst w. unfold w64. apply bv_eq. rewrite denot_SOff, Hn, unsigned_lit_small by exact Hz.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ps2_denot_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof.
intros E z Hz. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)).
rewrite U_lit by exact Hz. rewrite unsigned_lit_small by exact Hz. reflexivity.
Qed.
Lemma ps2_U_off : forall E n z v, bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> U E (SOff n z) = v + z.
Proof. intros E n z v Hn Hz. rewrite U_SOff, Hn. apply zcanon_id. unfold M64. lia. Qed.
(* memory outside a run's write windows is the memory before it *)
Definition ps2_wins_b (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  existsb (fun w => obase_eqb (YP09.r_base r) (Some (fst (fst w))) && (YP09.r_wlo r =? snd (fst w)) &&
                    (YP09.r_whi r =? snd w)) ws.
Lemma ps2_frame_wins : forall E rs m m' (ws : list (nat * Z * Z)),
  forallb (ps2_wins_b ws) rs = true -> frame_of E rs m m' ->
  forall x : word, Forall (fun w => ~ (bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= bv_unsigned x <
                                       bv_unsigned (ew E (fst (fst w))) + snd w)) ws -> m' x = m x.
Proof.
intros E rs m m' ws Hb HF x Hx. apply HF. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold ps2_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hw & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hx w Hw) as Hn. cbv beta in Hn.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hn. lia.
Qed.
Lemma ps2_mbyte_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  mbyte tfibsegs (mrestrict H m') x = mbyte tfibsegs (mrestrict H m) x.
Proof. intros H m m' x E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma ps2_wr_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  (writable_at tfibsegs (mrestrict H m) x <-> writable_at tfibsegs (mrestrict H m') x).
Proof. intros H m m' x E. unfold writable_at, wview, mrestrict. rewrite E. reflexivity. Qed.
Lemma ps2_bytes_at_eq : forall (H : word -> bool) m m' a bs,
  (forall k, (k < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  lib.Lib.Mem.bytes_at tfibsegs (mrestrict H m) a bs -> lib.Lib.Mem.bytes_at tfibsegs (mrestrict H m') a bs.
Proof.
intros H m m' a bs E (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros k Hk.
rewrite <- (H2 k Hk). unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa, mrestrict. rewrite (E k Hk). reflexivity.
Qed.
(* one byte of a region's 1-byte chunk *)
Lemma ps2_chunk1 : forall E m n lo hi wlo whi cs off v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal 1 v)) cs ->
  mbyte tfibsegs m (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 (bv_unsigned (sv_denot E v))).
Proof.
intros E m n lo hi wlo whi cs off v (_ & _ & _ & Hcs) Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.
Lemma ps2_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H Hc. subst r. apply H. reflexivity. Qed.
Lemma ps2_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma ps2_chunk1_ok : forall E m base off e (c : byte), sv_denot E e = w64 (bv_unsigned c) ->
  mbyte tfibsegs m (base + off) = Some c -> YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros E m base off e c He Hm i Hi. cbn [YP09.c_len YP09.c_val cv_len] in Hi.
assert (i = 0) by (change (Z.of_N 1) with 1 in Hi; lia). subst i. exists c. cbn [cbyte YP09.c_val YP09.c_off].
rewrite He. unfold byte_of_word, w64. rewrite Z.mul_0_r, Z.shiftr_0_r.
pose proof (YK11.u8_range c). rewrite unsigned_lit_small by lia. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. rewrite Z.add_0_r. exact Hm.
Qed.
(* a run's memory chain: every byte but the one window [v, v + 1) is the memory before the run *)
Lemma ps2_chain1 : forall E rs (m m' m0 : word -> option byte) (n : nat) v,
  frame_of E rs m m' -> forallb (ps2_wins_b [(n, 0, 1)]) rs = true -> bv_unsigned (ew E n) = v ->
  (forall x : word, bv_unsigned x <> v -> m x = m0 x) -> forall x : word, bv_unsigned x <> v -> m' x = m0 x.
Proof.
intros E rs m m' m0 n v HF Hb Hn HM x Hx. rewrite <- (HM x Hx).
apply (ps2_frame_wins E rs m m' [(n, 0, 1)] Hb HF x). constructor; [|constructor]. cbn [fst snd]. lia.
Qed.
Lemma ps2_awr_wins : forall E rs ws STK sp0 FP bl0 blc lyc own fr0,
  forallb (ps2_wins_b ws) rs = true ->
  Forall (fun w => forall x, bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= x <
    bv_unsigned (ew E (fst (fst w))) + snd w -> awr_byte tfibsegs B STK sp0 FP bl0 blc lyc own fr0 x) ws ->
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E rs ws STK sp0 FP bl0 blc lyc own fr0 Hb Hw x (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold ps2_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hwin & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hw w Hwin) as Hx. cbv beta in Hx.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hx. lia.
Qed.
(* the frame words of the 13 saved registers lie in [sp + 0x28, sp + 0x90) *)
Lemma ps2_frame_keep : forall (W : world tfibsegs) m m' regs0 sp,
  0 <= sp -> sp + 144 <= 2 ^ 64 ->
  (forall y, sp + 40 <= y < sp + 144 -> m' (Z_to_bv 64 y) = m (Z_to_bv 64 y)) ->
  pstr_frame_at W m regs0 sp -> pstr_frame_at W m' regs0 sp.
Proof.
intros W m m' regs0 sp H0 H1 HM HF. unfold pstr_frame_at in *.
assert (Hb : Forall (fun c => 40 <= fst c /\ fst c + 8 <= 144) pstr_saved)
  by (unfold pstr_saved; repeat constructor; cbn [fst]; lia).
rewrite Forall_forall in HF, Hb |- *. intros c Hc. apply (pstr_val_mem_eq_at _ m m'); [|exact (HF c Hc)].
intros k Hk. pose proof (Hb c Hc). apply HM. lia.
Qed.

(* ---- the copy loop's symbolic states (measured on the engine: pstr_q2.v) ---- *)
Definition ps2_srL : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 26%bv (SLit 34)) 14%bv (SLit 32)) 16%bv (SLit 92)) 25%bv
    (ps2_shx 9)) 23%bv (ps2_shx 8).
Definition ps2_rgL : list YP09.region :=
  [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
   YP09.mkRegion (Some 19%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]].
Definition ps2_faL : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3);
   (19%nat, mkAF 4096 0x7fffff800000 0); (20%nat, mkAF 4096 0x7fffff800000 0);
   (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 32 255 0); (33%nat, mkAF 0 (2 ^ 62) 0)] [] [].
Definition ps2_SHL : list shent := [mkSHE 19 0 1].
Definition ps2_ssL : sstate := mkSS 0x85200 ps2_srL ps2_rgL None ps2_faL.
(* the state at the return of fuzz_malloc 0x85184: the frame slots 8..0x20 (written) and in->end at s1 *)
Definition ps2_sr0 : list sv := sr_set sr_atoms 25%bv (ps2_shx 9).
Definition ps2_rg0 : list YP09.region :=
  [YP09.mkRegion (Some 2%nat) 8 32 8 32 [];
   YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]].
Definition ps2_fa0 : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (10%nat, mkAF 4112 0x7fffff800000 4);
   (20%nat, mkAF 4096 0x7fffff800000 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 62) 0)] [] [].
Definition ps2_ss0 : sstate := mkSS 0x85184 ps2_sr0 ps2_rg0 None ps2_fa0.
Lemma ps2_chainw : forall E rs (m m' m0 : word -> option byte) (n : nat) lo hi v,
  frame_of E rs m m' -> forallb (ps2_wins_b [(n, lo, hi)]) rs = true -> bv_unsigned (ew E n) = v ->
  (forall x : word, ~ (v + lo <= bv_unsigned x < v + hi) -> m x = m0 x) ->
  forall x : word, ~ (v + lo <= bv_unsigned x < v + hi) -> m' x = m0 x.
Proof.
intros E rs m m' m0 n lo hi v HF Hb Hn HM x Hx. rewrite <- (HM x Hx).
apply (ps2_frame_wins E rs m m' [(n, lo, hi)] Hb HF x). constructor; [|constructor]. cbn [fst snd]. lia.
Qed.

(* the exit state at the loop head when the byte is the closing quote: the quote at s4, the NUL's byte at s3, in->p at
   s0 (written), and the 13 frame words the epilogue reloads (extra atoms 32 .. 44, pstr_saved's order) *)
Definition ps2_fchunks : list YP09.chunk :=
  [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x78 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x68 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 37 0));
   YP09.mkChunk 0x58 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 39 0));
   YP09.mkChunk 0x48 (CVal 8 (SOff 40 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 41 0));
   YP09.mkChunk 0x38 (CVal 8 (SOff 42 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 43 0));
   YP09.mkChunk 0x28 (CVal 8 (SOff 44 0))].
Definition ps2_rgX : list YP09.region :=
  [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 34))];
   YP09.mkRegion (Some 19%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 8%nat) 0 8 0 8 [];
   YP09.mkRegion (Some 2%nat) 40 144 0 0 ps2_fchunks].
Definition ps2_faX : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
   (19%nat, mkAF 4096 0x7fffff800000 0); (20%nat, mkAF 4096 0x7fffff800000 0);
   (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ps2_ssX : sstate := mkSS 0x85200 ps2_srL ps2_rgX None ps2_faX.
Definition ps2_xsX (regs0 : bvmap 5 word) : list word := map (fun c => YK11.getr regs0 (Z_to_bv 5 (snd c))) pstr_saved.
(* what the run leaves in each callee-saved register at the `ret` *)
Definition ps2_expect (r : bv 5) : sv :=
  let z := bv_unsigned r in
  if z =? 2 then SOff 2 144 else if z =? 3 then SOff 3 0 else if z =? 4 then SOff 4 0
  else if z =? 8 then SOff 33 0 else if z =? 9 then SOff 34 0 else SOff (Z.to_nat (z + 17)) 0.
Lemma ps2_fchunk : forall E m sp off (n : nat) v, val_mem tfibsegs m (sp + off) 8 v ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok tfibsegs E m sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m sp off n v Hv He Hr. apply (chunk_ok_val tfibsegs E m sp off 8 (SOff n 0) v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
exact Hv.
Qed.

(* the last loaded segment of fs.asan, [0xa1000, 0x5fd000), holds fuzz/alloc.c's statics *)
Lemma ps2_img_hi : forall x, 0xa1000 <= x < 0x5fd000 -> in_img tfibsegs x.
Proof.
intros x Hx.
assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) =? 659456) && (Z.of_N (seg_size sg) =? 5619712)) tfibsegs = true)
  by (vm_compute; reflexivity).
apply existsb_exists in Hb as (sg & Hin & Hsg). apply andb_prop in Hsg as [H1 H2]. apply Z.eqb_eq in H1, H2.
exists sg. split; [exact Hin | lia].
Qed.

Section L.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ot q text len p d : Z) (tb : list byte) (tcap Q live peak cnt fail a : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (mem2 : word -> option byte).
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis HSPal : spZ regs mod 16 = 0.
Hypothesis Hceil : alloc_ceiling <= ly_stk_lo ly.
Hypothesis HSTK : ly_stk_lo ly + STK_parse_string <= spZ regs.
Hypothesis Hot : ot <= ly_stk_hi ly.
Hypothesis H47 : ly_stk_hi ly <= 2 ^ 47.
Hypothesis Hq1 : spZ regs <= q.
Hypothesis Hq2 : q + 24 <= ot.
Hypothesis Hlo2 : ly_stk_lo ly2 = ly_stk_lo ly.
Hypothesis Hhi2 : ly_stk_hi ly2 = ly_stk_hi ly.
Hypothesis HIN2 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len p d tb.
Hypothesis HTX2 : rd_text tfibsegs B ly2 S2 W2 mem2 text len tcap.
Hypothesis HTX1 : In (text - HEAD, tcap + HEAD) (ablocks B ly S).
Hypothesis Hrun : plain_run tb text len p Q.
Hypothesis Hab : ablocks B ly2 S2 = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)].
Hypothesis Ha16 : 4096 + HEAD <= a.
Hypothesis Ham : a mod 16 = 0.
Hypothesis HRB : fs_rblock tfibsegs B ly2 S2 W2 mem2 a (Q + 1).
Hypothesis HFH : FSupoisonU.fs_heads B ly2 S2 (U ++ [(a - HEAD, HEAD)]).
Hypothesis HWK : wkeep tfibsegs W W2 mem mem2 (spZ regs) ot q 24.
Hypothesis HGL : fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail.
(* the new block against the old ones (from AR at the return, ps2_blocks below) *)
Hypothesis Hnew : ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S).
Hypothesis Hdisj : text + tcap <= a - HEAD \/ a + Q + 1 <= text - HEAD.
Hypothesis Hceil_a : a + Q + 1 <= alloc_ceiling.
Hypothesis Hceil_t : text + tcap <= alloc_ceiling.
Hypothesis Happ : a + Q + 1 <= kLowShadowBeg \/ kHighMemBeg <= a - HEAD.
Hypothesis Himg : forall x, a - HEAD <= x < a + Q + 1 -> ~ in_img tfibsegs x.

Definition ps2_U2 : list (Z * Z) := U ++ [(a - HEAD, HEAD)].
Definition ps2_STKw : Z := STK_parse_string + (ot - spZ regs).
Definition ps2_PQ : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    YK11.getr regs' 10 = w64 a /\ 4096 + HEAD <= a /\
    ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
    fs_rblock tfibsegs B ly' S' W' mem' a (Q + 1) /\
    PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a (run_at tb text p Q) /\
    PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Q + 2) d tb /\
    wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
    rd_text tfibsegs B ly' S' W' mem' text len tcap /\
    fs_glob tfibsegs W' mem' (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail.
Definition ps2_POST : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B ps2_STKw ot FS_PSTAT_FP regs ly S U W mem md EV_fuzz_malloc ps2_U2 ps2_PQ.
(* the copy loop's head 0x85200 after i copied bytes, as machine facts *)
Definition ps2_LH (i : Z) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  spZ regsL = spZ regs - FRAME_PSTR /\
  YK11.getr regsL 3 = YK11.getr regs 3 /\ YK11.getr regsL 4 = YK11.getr regs 4 /\
  YK11.getr regsL 8 = w64 q /\ YK11.getr regsL 9 = w64 (q + 8) /\
  YK11.getr regsL 18 = w64 a /\ YK11.getr regsL 19 = w64 (a + i) /\ YK11.getr regsL 20 = w64 (p + 1 + i) /\
  YK11.getr regsL 23 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regsL 24 = w64 SHADOW_OFF /\
  YK11.getr regsL 25 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  YK11.getr regsL 26 = w64 34 /\ YK11.getr regsL 14 = w64 32 /\ YK11.getr regsL 16 = w64 92 /\
  pstr_frame_at W2 memL regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B ps2_STKw ot FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 W2 (unpoison ps2_U2 memL) mdL
    EV_fuzz_malloc /\
  ARU tfibsegs B ly2 S2 ps2_U2 W2 memL mdL /\
  (forall x : word, ~ (a <= bv_unsigned x < a + i) -> ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) ->
     memL x = mem2 x) /\
  (forall j, 0 <= j < i -> mbyte tfibsegs (mrestrict (w_H W2) memL) (a + j) = nth_error tb (Z.to_nat (p + 1 + j - text))).

(* ---- the numeric facts of the premises ---- *)
Lemma ps2_nums : 0 <= Q /\ p + 1 + Q < text + len /\ text <= p /\ text + len < 2 ^ 62 /\ q mod 8 = 0 /\
  Z.of_nat (length tb) = len /\ 4096 + HEAD <= text /\ len < tcap /\ text mod 16 = 0 /\
  In (text - HEAD, tcap + HEAD) (ablocks B ly2 S2) /\ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2) /\
  STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v) /\ alloc_ceiling <= spZ regs - STK_parse_string /\ spZ regs <= 2 ^ 47 /\
  140735332483072 <= alloc_ceiling <= 140737479966720 /\ kHighMemBeg = 17594333495296.
Proof.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
pose proof Hrun as (R0 & R1 & _). pose proof HTX2 as (T0 & (T1 & T2 & T3 & _) & T4).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (Hin : In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (E : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v)) by (vm_compute; reflexivity).
repeat split; try assumption; lia.
Qed.
Lemma ps2_text_byte : forall k, 0 <= k < len ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) (text + k) = nth_error tb (Z.to_nat k).
Proof.
intros k Hk. pose proof ps2_nums as (_ & _ & _ & _ & _ & Hl & _).
pose proof HIN2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hb) & _).
specialize (Hb (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. exact Hb.
Qed.
(* the copy's bytes are writable on the machine's memory (live block bytes, no head covers them) *)
Lemma ps2_heap_wr : forall memX mdX x, ARU tfibsegs B ly2 S2 ps2_U2 W2 memX mdX -> a <= x < a + Q + 1 ->
  writable_at tfibsegs (mrestrict (w_H W2) memX) x.
Proof.
intros memX mdX x HARU Hx. pose proof ps2_nums as (N0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hin & _ & _ & _ & C1 & C3).
pose proof HARU as (HAR & _ & _). pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ mdX _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
rewrite ps2_req in Hpres by (unfold HEAD; lia).
destruct (Hpres x ltac:(unfold HEAD in *; lia)) as [(Hh & b & Hb) _].
apply apresent_writable. split; [exact Hh|]. exists b. rewrite <- Hb. symmetry. apply unpoison_out.
rewrite (wz x ltac:(unfold HEAD in *; lia)). destruct (in_ush ps2_U2 x) eqn:Eu; [exfalso|reflexivity].
pose proof (ush_facts tfibsegs B ly2 S2 ps2_U2 W2 memX mdX x HARU Eu) as (_ & L1 & L2).
unfold HEAD, kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
(* in->end on the loop's memory *)
Lemma ps2_in_end : forall memL, (forall y, q <= y < q + 24 -> memL (Z_to_bv 64 y) = mem2 (Z_to_bv 64 y)) ->
  val_mem tfibsegs (mrestrict (w_H W2) memL) (q + 8) 8 (text + len).
Proof.
intros memL HM. pose proof ps2_nums as (_ & _ & _ & HT & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
pose proof HIN2 as (_ & Hend & _).
apply (pstr_val_mem_eq_at _ mem2 memL); [intros k Hk; apply HM; lia|].
apply (proj2 (val_mem_word_mem tfibsegs _ _ _)).
pose proof (KindBGlue.bytes_at_le8_word tfibsegs _ _ _ Hend) as Hw. rewrite unsigned_lit_small in Hw by lia. exact Hw.
Qed.
Lemma ps2_reg_keep : forall (H : word -> bool) E ss ms (r : bv 5) (n : nat) regsL extra,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = ew (Ereg regsL extra) n ->
  Z.of_nat n = bv_unsigned r -> YK11.getr (ms_regs ms) r = YK11.getr regsL r.
Proof.
intros H E ss ms r n regsL extra HS Hr Hn Hnr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, fsw_SOff0, Hn.
exact (ew_Ereg_nat regsL extra n r Hnr).
Qed.
Lemma ps2_spZ : forall regs0 v, YK11.getr regs0 2 = w64 v -> 0 <= v < 2 ^ 64 -> spZ regs0 = v.
Proof. intros regs0 v H Hv. unfold spZ. rewrite H. unfold w64. apply unsigned_lit_small; exact Hv. Qed.

Ltac ps2_ews := repeat rewrite ew_ewset_other by lia.
Ltac ps2_ews_in H := repeat rewrite ew_ewset_other in H by lia.

(* ---- one turn of the copy loop: byte i is plain, copied to a + i, and the loop goes back to 0x85200 ---- *)
Lemma ps2_step : forall i regsL memL mdL, 0 <= i < Q -> ps2_LH i regsL memL mdL ->
  (forall regs' mem' md', ps2_LH (i + 1) regs' mem' md' ->
     SRr tfibsegs W2 (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x85200) mem' (YK11.seg_rom tfibsegs)) md') ps2_POST) ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85200) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
intros i regsL memL mdL Hi HL HK.
destruct HL as (Lsp & L3 & L4 & L8 & L9 & L18 & L19 & L20 & L23 & L24 & L25 & L26 & L14 & L16 & LF & HJ & HARU & LM & LB).
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity. assert (ELS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof Hrun as (_ & _ & _ & Hpl). destruct (Hpl i Hi) as (c & Hcb & Hcp). unfold plain_byte in Hcp.
pose proof (YK11.u8_range c) as Hc8.
assert (EW32 : ew (Ereg regsL [w64 (bv_unsigned c); w64 (text + len)]) 32 = w64 (bv_unsigned c)) by reflexivity.
assert (EW33 : ew (Ereg regsL [w64 (bv_unsigned c); w64 (text + len)]) 33 = w64 (text + len)) by reflexivity.
set (xs := [w64 (bv_unsigned c); w64 (text + len)]) in EW32, EW33.
assert (E2 : bv_unsigned (ew (Ereg regsL xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regsL xs 2 2%bv eq_refl); exact Lsp).
assert (E8 : bv_unsigned (ew (Ereg regsL xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact L8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regsL xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact L9 | lia]).
assert (E18 : bv_unsigned (ew (Ereg regsL xs) 18) = a) by (apply (ps2_ewR _ _ 18 18%bv); [reflexivity | exact L18 | lia]).
assert (E19 : bv_unsigned (ew (Ereg regsL xs) 19) = a + i)
  by (apply (ps2_ewR _ _ 19 19%bv); [reflexivity | exact L19 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regsL xs) 20) = p + 1 + i)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact L20 | lia]).
assert (E24 : bv_unsigned (ew (Ereg regsL xs) 24) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 24 24%bv); [reflexivity | exact L24 | unfold SHADOW_OFF; lia]).
assert (E32 : bv_unsigned (ew (Ereg regsL xs) 32) = bv_unsigned c)
  by (rewrite EW32; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : bv_unsigned (ew (Ereg regsL xs) 33) = text + len)
  by (rewrite EW33; unfold w64; apply unsigned_lit_small; lia).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
assert (M9 : (q + 8) mod 8 = 0) by (replace (q + 8) with (q + 1 * 8) by lia; rewrite Z_mod_plus_full; exact N4).
assert (HS : st_ok tfibsegs (Ereg regsL xs) ps2_ssL
  (restrict (w_H W2) (YK11.mkst regsL (Z_to_bv 64 0x85200) memL (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ssL. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_srL.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 8 q E8 E24 ltac:(lia)); exact L23].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E24 ltac:(lia)); exact L25].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L16].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L14].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L26].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rgL. constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E20.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (ps2_chunk1_ok _ _ _ _ _ c); [rewrite fsw_SOff0; exact EW32|].
      rewrite Z.add_0_r. rewrite (ps2_mbyte_eq _ mem2 memL) by (apply LM; rewrite wz by lia; lia).
      replace (p + 1 + i) with (text + (p + 1 + i - text)) by lia. rewrite ps2_text_byte by lia.
      replace (text + (p + 1 + i - text)) with (p + 1 + i) by lia. exact Hcb.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (ps2_heap_wr memL mdL); [exact HARU | lia]|].
      constructor.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (q + 8) 0 8 (SOff 33 0) (text + len));
        [rewrite fsw_SOff0; exact EW33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. apply ps2_in_end.
      intros y Hy. apply LM; rewrite wz by lia; lia.
  - unfold ps2_rgL. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E19, E20, E9. repeat split; lia.
  - unfold ps2_faL. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E9, E19, E20, E24, E32, E33.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; exact M2
      | change (2 ^ 3) with 8; first [exact N4 | exact M9]]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq ps2_SHL (Ereg regsL xs) (mrestrict (w_H W2) memL)).
{ unfold sh_ok, ps2_SHL. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold ps2_Bq.
  rewrite (ps2_U_off _ 24 0 SHADOW_OFF E24) by (unfold SHADOW_OFF; lia).
  rewrite (ps2_U_off _ 19 0 (a + i) E19) by lia. split.
  - rewrite !Z.add_0_r. replace (1 - 0) with 1 by lia.
    exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (a - HEAD) (Q + 1 + HEAD) (a + i) 1 HARU HFH HinA
      ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)).
  - intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy. lia. }
assert (HM : forall x : word, bv_unsigned x <> a + i -> memL x = memL x) by (intros; reflexivity).
(* run 1: to the `beq a2, s10` at 0x85214 *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff, E24, E20, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (text - HEAD) (tcap + HEAD) (p + 1 + i) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) E19 HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the closing quote? no: c <> 34 *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
{ exfalso. rewrite branch_eq_U, U_SOff, U_SLit in Hc. ps2_ews_in Hc. rewrite E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* run 2: to the `bne a0, a6` at 0x8522c *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff. ps2_ews. rewrite E24, E20, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 _ _ (text - HEAD) (tcap + HEAD) (p + 1 + i) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* no escape: c <> 0x5c *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
2: { exfalso. rewrite branch_ne_U, U_SOff, U_SLit in Hc. ps2_ews_in Hc. rewrite E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc. lia. }
clear Hc.
(* run 3: the store to a + i and the in->end reload, to the `bltu s6, a1` at 0x85420 *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff. ps2_ews. rewrite E24, E9, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ (q + 8) 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) M9 eq_refl ltac:(lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the loop goes on: p + 1 + i + 1 < text + len *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
2: { exfalso. rewrite branch_ltu_U, !U_SOff in Hc. ps2_ews_in Hc. rewrite E20, E33 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. lia. }
clear Hc.
(* run 4: the taken branch back to the loop head *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85200.
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the copied byte *)
pose proof (fsw_region_nth _ _ _ 1 (YP09.mkRegion (Some 19%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]) HS
  ltac:(vm_compute; reflexivity)) as RO.
pose proof (ps2_chunk1 _ _ _ _ _ _ _ _ 0 (SOff 32 0) RO ltac:(left; reflexivity)) as HB. clear RO.
rewrite fsw_SOff0 in HB. ps2_ews_in HB. rewrite E19, Z.add_0_r, EW32 in HB.
unfold w64 in HB. rewrite unsigned_lit_small, Z_to_bv_bv_unsigned in HB by lia.
pose proof (@st_ok_restrict_mkst tfibsegs _ (w_H W2) _ _ _ HS eq_refl) as Hshape. rewrite Hshape.
apply HK. unfold ps2_LH.
rewrite ?wvb_collapse in HJ, HARU.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj HJ (conj HARU (conj _ _)))))))))))))))))).
- apply ps2_spZ; [|lia]. apply (ps2_reg_val _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (spZ regs - FRAME_PSTR)); [ps2_ews; exact E2 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 3%bv 3 regsL xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact L3.
- rewrite (ps2_reg_keep _ _ _ _ 4%bv 4 regsL xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact L4.
- apply (ps2_reg_val _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ q); [ps2_ews; exact E8 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 9%bv (SOff 9 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (q + 8)); [ps2_ews; exact E9 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 18%bv (SOff 18 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E18 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 19%bv (SOff 19 1) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (a + i)); [ps2_ews; exact E19 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 20%bv (SOff 20 1) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (p + 1 + i)); [ps2_ews; exact E20 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 23%bv (ps2_shx 8) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E8 | ps2_ews; exact E24 | lia].
- apply (ps2_reg_val _ _ _ _ 24%bv (SOff 24 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ SHADOW_OFF); [ps2_ews; exact E24 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 25%bv (ps2_shx 9) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E9 | ps2_ews; exact E24 | lia].
- apply (ps2_reg_val _ _ _ _ 26%bv (SLit 34) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 14%bv (SLit 32) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 16%bv (SLit 92) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_frame_keep W2 memL); [lia | lia | | exact LF]. intros y Hy. apply HM. rewrite wz by lia. lia.
- intros x Hx1 Hx2. rewrite (HM x ltac:(lia)). apply LM; lia.
- intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
  + rewrite Hcb. exact HB.
  + rewrite (ps2_mbyte_eq _ memL) by (apply HM; rewrite wz by lia; lia). apply LB. lia.
Qed.

(* ---- the post's memory facts from the final memory: it is mem2 outside the copy [a, a + Q], the frame and in->p ---- *)
Lemma ps2_post : forall regsF memF mdF,
  (forall x : word, ~ (a <= bv_unsigned x < a + Q + 1) -> ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) ->
     ~ (q <= bv_unsigned x < q + 8) -> memF x = mem2 x) ->
  (forall j, 0 <= j < Q ->
     mbyte tfibsegs (mrestrict (w_H W2) memF) (a + j) = nth_error tb (Z.to_nat (p + 1 + j - text))) ->
  mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Q) = Some (Z_to_bv 8 0) ->
  val_mem tfibsegs (mrestrict (w_H W2) memF) q 8 (p + Q + 2) ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W2) memF) (q + o)) ->
  YK11.getr regsF 10 = w64 a ->
  ps2_PQ ly2 S2 W2 regsF memF mdF.
Proof.
intros regsF memF mdF HMF HBY HNUL HP HPW H10.
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
pose proof Hrun as (_ & _ & _ & Hpl).
assert (EH : HEAD = 16) by reflexivity. assert (EFP : FRAME_PSTR = 144) by reflexivity.
assert (KEEP : forall y, 0 <= y < 2 ^ 64 -> ~ (a <= y < a + Q + 1) -> ~ (spZ regs - FRAME_PSTR <= y < spZ regs) ->
  ~ (q <= y < q + 8) -> memF (Z_to_bv 64 y) = mem2 (Z_to_bv 64 y)).
{ intros y Hy H1 H2 H3. apply HMF; rewrite wz by lia; lia. }
set (k0 := Z.to_nat (p + 1 - text)).
assert (RUN : forall j, (j < Z.to_nat Q)%nat ->
  nth_error (firstn (Z.to_nat Q) (skipn k0 tb)) j = nth_error tb (Z.to_nat (p + 1 + Z.of_nat j - text))).
{ intros j Hj. rewrite nth_error_firstn. replace (j <? Z.to_nat Q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_error_skipn. f_equal. unfold k0. lia. }
assert (LRUN : length (firstn (Z.to_nat Q) (skipn k0 tb)) = Z.to_nat Q).
{ apply firstn_length_le. rewrite length_skipn. unfold k0. lia. }
unfold ps2_PQ.
split; [exact H10|]. split; [exact Ha16|]. split; [exact Hab|].
split.
{ destruct HRB as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  apply (pstr_val_mem_eq_at _ mem2 memF); [|exact R4]. intros k Hk. apply KEEP; lia. }
split.
{ unfold PjStruct.pj_cbytes, run_at, ReaderRes.zb. fold k0. split.
  - apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
    apply In_nth_error in Hb as (j & Hj).
    assert (Hjl : (j < Z.to_nat Q)%nat) by (rewrite <- LRUN; apply nth_error_Some; congruence).
    rewrite (RUN j Hjl) in Hj. destruct (Hpl (Z.of_nat j) ltac:(lia)) as (c' & Hc' & Hpc').
    rewrite Hj in Hc'. injection Hc' as <-. unfold plain_byte in Hpc'. pose proof (YK11.u8_range b). lia.
  - split; [lia|]. rewrite length_map, length_app, length_map, LRUN. cbn [length]. split; [lia|].
    intros j Hj. rewrite nth_error_map. destruct (Nat.lt_ge_cases j (Z.to_nat Q)) as [Hjq|Hjq].
    + rewrite nth_error_app1 by (rewrite length_map, LRUN; lia). rewrite nth_error_map, RUN by exact Hjq.
      transitivity (mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Z.of_nat j)); [reflexivity|].
      rewrite HBY by lia. destruct (Hpl (Z.of_nat j) ltac:(lia)) as (c' & Hc' & _). rewrite Hc'. cbn [option_map].
      rewrite Z_to_bv_bv_unsigned. reflexivity.
    + assert (j = Z.to_nat Q) by lia. subst j.
      rewrite nth_error_app2 by (rewrite length_map, LRUN; lia). rewrite length_map, LRUN, Nat.sub_diag.
      cbn [nth_error option_map].
      transitivity (mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Z.of_nat (Z.to_nat Q))); [reflexivity|].
      rewrite Z2Nat.id by lia. exact HNUL. }
split.
{ destruct HIN2 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
  refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
  - apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HP | lia | lia | lia].
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I2]. intros k Hk. rewrite lib.Lib.Mem.length_le8 in Hk.
    apply KEEP; lia.
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I3]. intros k Hk. rewrite lib.Lib.Mem.length_le4 in Hk.
    apply KEEP; lia.
  - destruct I4 as (W1 & W1' & W3). split; [lia|]. split; [lia|]. intros o Ho.
    destruct (Z_lt_le_dec o 8) as [Ho8|Ho8]; [exact (HPW o ltac:(lia))|].
    apply (ps2_wr_eq _ mem2 memF (q + o)); [apply KEEP; lia | exact (W3 o Ho)].
  - lia.
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I10]. intros k Hk. apply KEEP; lia. }
split.
{ intros x Hx Hnq. destruct (HWK x Hx Hnq) as [K1 K2].
  assert (Ex : memF (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)) by (apply KEEP; lia).
  split; [rewrite (ps2_mbyte_eq _ mem2 memF x Ex); exact K1|].
  rewrite K2. exact (ps2_wr_eq _ mem2 memF x Ex). }
split.
{ destruct HTX2 as (T0 & (T1 & T2 & T3 & T4) & T5). split; [exact T0|]. split; [|exact T5].
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
  apply (pstr_val_mem_eq_at _ mem2 memF); [|exact T4]. intros k Hk. apply KEEP; lia. }
assert (GK : forall g v, 0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) memF) g 8 v).
{ intros g v Hg1 Hg2 Hv. apply (pstr_val_mem_eq_at _ mem2 memF); [|exact Hv]. intros k Hk. apply KEEP; [lia | | lia | lia].
  intros Hin. apply (Himg (g + Z.of_nat k)); [lia | apply ps2_img_hi; lia]. }
destruct HGL as (G1 & G2 & G3 & G4 & GR). cbv [fs_glob fs_glob_at].
split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
exact GR.
Qed.

(* ---- the exit: the byte at the read cursor is the closing quote; the NUL, in->p := p + Q + 2, the epilogue, `ret` ---- *)
Lemma ps2_exit : forall regsL memL mdL, ps2_LH Q regsL memL mdL ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85200) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
intros regsL memL mdL HL.
destruct HL as (Lsp & L3 & L4 & L8 & L9 & L18 & L19 & L20 & L23 & L24 & L25 & L26 & L14 & L16 & LF & HJ & HARU & LM & LB).
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity. assert (ELS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof Hrun as (_ & _ & Rq & _).
set (xs := ps2_xsX regs).
assert (E2 : bv_unsigned (ew (Ereg regsL xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regsL xs 2 2%bv eq_refl); exact Lsp).
assert (E8 : bv_unsigned (ew (Ereg regsL xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact L8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regsL xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact L9 | lia]).
assert (E18 : bv_unsigned (ew (Ereg regsL xs) 18) = a) by (apply (ps2_ewR _ _ 18 18%bv); [reflexivity | exact L18 | lia]).
assert (E19 : bv_unsigned (ew (Ereg regsL xs) 19) = a + Q)
  by (apply (ps2_ewR _ _ 19 19%bv); [reflexivity | exact L19 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regsL xs) 20) = p + 1 + Q)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact L20 | lia]).
assert (E24 : bv_unsigned (ew (Ereg regsL xs) 24) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 24 24%bv); [reflexivity | exact L24 | unfold SHADOW_OFF; lia]).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
pose proof LF as LF'. unfold pstr_frame_at, pstr_saved in LF'.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *.
assert (HS : st_ok tfibsegs (Ereg regsL xs) ps2_ssX
  (restrict (w_H W2) (YK11.mkst regsL (Z_to_bv 64 0x85200) memL (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ssX. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_srL.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 8 q E8 E24 ltac:(lia)); exact L23].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E24 ltac:(lia)); exact L25].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L16].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L14].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L26].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rgX. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E20.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (ps2_chunk1_ok _ _ _ _ _ (Z_to_bv 8 34)); [rewrite ps2_denot_lit by lia; reflexivity|].
      rewrite Z.add_0_r. rewrite (ps2_mbyte_eq _ mem2 memL) by (apply LM; rewrite wz by lia; lia).
      replace (p + 1 + Q) with (text + (p + 1 + Q - text)) by lia. rewrite ps2_text_byte by lia.
      replace (text + (p + 1 + Q - text) - text) with (p + 1 + Q - text) in Rq by lia.
      replace (p + 1 + Q - text) with (p + 1 + Q - text) by lia. exact Rq.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (ps2_heap_wr memL mdL); [exact HARU | lia]|].
      constructor.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho.
      pose proof HIN2 as (_ & _ & _ & (W1 & W1' & W3) & _).
      apply (ps2_wr_eq _ mem2 memL (q + o)); [apply LM; rewrite wz by lia; lia | exact (W3 o ltac:(lia))].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. unfold ps2_fchunks.
      repeat (apply Forall_cons; [eapply ps2_fchunk; [eassumption | rewrite fsw_SOff0, Z_to_bv_bv_unsigned; reflexivity
        | apply YK11.u64_range] |]).
      apply Forall_nil.
  - unfold ps2_rgX. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E19, E20, E8, E2. repeat split; lia.
  - unfold ps2_faX. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E19, E20, E24.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; exact M2
      | change (2 ^ 3) with 8; exact N4]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq ps2_SHL (Ereg regsL xs) (mrestrict (w_H W2) memL)).
{ unfold sh_ok, ps2_SHL. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold ps2_Bq.
  rewrite (ps2_U_off _ 24 0 SHADOW_OFF E24) by (unfold SHADOW_OFF; lia).
  rewrite (ps2_U_off _ 19 0 (a + Q) E19) by lia. split.
  - rewrite !Z.add_0_r. replace (1 - 0) with 1 by lia.
    exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (a - HEAD) (Q + 1 + HEAD) (a + Q) 1 HARU HFH HinA
      ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)).
  - intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy. lia. }
(* one run: the closing quote, the NUL, in->p, the epilogue, to the `ret` at 0x855fc *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x855fc.
{ unfold ps2_Bq. rewrite !U_SOff, E24, E8, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ q 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) N4 eq_refl ltac:(lia)). }
{ unfold ps2_Bq. rewrite !U_SOff, E24, E20, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (text - HEAD) (tcap + HEAD) (p + 1 + Q) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1); (8%nat, 0, 8)]); [vm_compute; reflexivity|].
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx.
  - rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
    split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia.
  - rewrite E8 in Hx. left; left. unfold ps2_STKw. lia. }
match goal with HS0 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msf end.
assert (HMF : forall x : word, ~ (a + Q <= bv_unsigned x < a + Q + 1) -> ~ (q <= bv_unsigned x < q + 8) ->
  ms_mem msf x = memL x).
{ intros x Hy1 Hy2. refine (ps2_frame_wins _ _ _ _ [(19%nat, 0, 1); (8%nat, 0, 8)] _ HF x _); [vm_compute; reflexivity|].
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; [rewrite E19 | rewrite E8]; lia. }
pose proof (fsw_region_nth _ _ _ 1 (YP09.mkRegion (Some 19%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS
  ltac:(vm_compute; reflexivity)) as RO.
pose proof (ps2_chunk1 _ _ _ _ _ _ _ _ 0 (SLit 0) RO ltac:(left; reflexivity)) as HB0. clear RO.
ps2_ews_in HB0. rewrite E19, Z.add_0_r, ps2_denot_lit in HB0 by lia. unfold w64 in HB0.
rewrite unsigned_lit_small in HB0 by lia.
pose proof (fsw_region_nth _ _ _ 2 (YP09.mkRegion (Some 8%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 20 1))]) HS
  ltac:(vm_compute; reflexivity)) as RP.
pose proof (fsw_field _ _ _ q _ _ _ _ _ 0 8 (SOff 20 1) (p + Q + 2) RP ltac:(ps2_ews; exact E8)
  ltac:(left; reflexivity) ltac:(apply (ps2_denot_off _ _ _ (p + 1 + Q)); [ps2_ews; exact E20 | lia | lia])
  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as HPV.
rewrite Z.add_0_r in HPV.
destruct RP as (_ & _ & RPW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RPW. ps2_ews_in RPW.
rewrite E8 in RPW.
unfold ps2_POST.
refine (fsw_retU B parse_string_tbl parse_string_tbl_ok W2 _ _ msf _ ps2_STKw ot FS_PSTAT_FP regs ly S U W mem md
  ly2 S2 ps2_U2 EV_fuzz_malloc ps2_PQ HS eq_refl ltac:(vm_compute; reflexivity) _ HJ HARU _ _).
- rewrite (st_ok_restrict_reg tfibsegs _ _ _ msf 1%bv HS).
  match goal with |- context [sr_get ?l 1%bv] => replace (sr_get l 1%bv) with (SOff 32 0) by (vm_compute; reflexivity) end.
  rewrite fsw_SOff0. ps2_ews. exact Hra.
- apply (fsw_preserved _ _ _ msf regs ps2_expect HS); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: lazymatch goal with |- sv_denot _ (ps2_expect ?r) = _ =>
    let e := eval vm_compute in (ps2_expect r) in change (ps2_expect r) with e end.
  all: first
    [ rewrite fsw_SOff0; ps2_ews; reflexivity
    | rewrite fsw_SOff0; ps2_ews; rewrite (ew_Ereg_nat regsL xs 3 3%bv eq_refl); exact L3
    | rewrite fsw_SOff0; ps2_ews; rewrite (ew_Ereg_nat regsL xs 4 4%bv eq_refl); exact L4
    | apply bv_eq; rewrite denot_SOff; ps2_ews; rewrite E2; change (bv_unsigned (YK11.getr regs 2%bv)) with (spZ regs);
      rewrite zcanon_id by (unfold M64; lia); lia ].
- intros mat0. apply ps2_post.
  + intros x Hx1 Hx2 Hx3. rewrite (HMF x ltac:(lia) Hx3). apply LM; lia.
  + intros j Hj. rewrite (ps2_mbyte_eq _ memL) by (apply HMF; rewrite wz by lia; lia). apply LB. lia.
  + exact HB0.
  + exact HPV.
  + intros o Ho. exact (RPW o Ho).
  + apply (ps2_reg_val _ _ _ _ 10%bv (SOff 18 0) _ HS); [vm_compute; reflexivity|].
    apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E18 | lia | lia].
Qed.

(* ---- the copy loop: induction over the bytes left ---- *)
Lemma ps2_loop : forall n i regsL memL mdL, Z.to_nat (Q - i) = n -> 0 <= i <= Q -> ps2_LH i regsL memL mdL ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85200) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
induction n as [|n IH]; intros i regsL memL mdL Hn Hi HL.
- assert (i = Q) by lia. subst i. exact (ps2_exit regsL memL mdL HL).
- apply (ps2_step i regsL memL mdL ltac:(lia) HL). intros regs' mem' md' HL'.
  apply (IH (i + 1) regs' mem' md'); [lia | lia | exact HL'].
Qed.

(* ---- from the return of fuzz_malloc 0x85184 to the loop head 0x85200 (the a0 test, in->end, the constants) ---- *)
Lemma ps2_r0 : forall regs2 md2,
  spZ regs2 = spZ regs - FRAME_PSTR -> YK11.getr regs2 10 = w64 a ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = w64 q -> YK11.getr regs2 9 = w64 (q + 8) -> YK11.getr regs2 20 = w64 (p + 1) ->
  YK11.getr regs2 23 = w64 (SHADOW_OFF + q / 8) -> YK11.getr regs2 24 = w64 SHADOW_OFF ->
  YK11.getr regs2 25 = w64 (SHADOW_OFF + (q + 8) / 8) ->
  pstr_frame_at W2 mem2 regs (spZ regs - FRAME_PSTR) ->
  ajournal tfibsegs B ps2_STKw ot FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 W2 (unpoison ps2_U2 mem2) md2
    EV_fuzz_malloc ->
  ARU tfibsegs B ly2 S2 ps2_U2 W2 mem2 md2 ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2) ps2_POST.
Proof using All.
intros regs2 md2 Rsp R10 R3 R4 R8 R9 R20 R23 R24 R25 RF HJ HARU.
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity.
set (xs := [w64 (text + len)]).
assert (EW32 : ew (Ereg regs2 xs) 32 = w64 (text + len)) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs2 xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regs2 xs 2 2%bv eq_refl); exact Rsp).
assert (E8 : bv_unsigned (ew (Ereg regs2 xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact R8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regs2 xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact R9 | lia]).
assert (E10 : bv_unsigned (ew (Ereg regs2 xs) 10) = a) by (apply (ps2_ewR _ _ 10 10%bv); [reflexivity | exact R10 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regs2 xs) 20) = p + 1)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact R20 | lia]).
assert (E24 : bv_unsigned (ew (Ereg regs2 xs) 24) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 24 24%bv); [reflexivity | exact R24 | lia]).
assert (E32 : bv_unsigned (ew (Ereg regs2 xs) 32) = text + len)
  by (rewrite EW32; unfold w64; apply unsigned_lit_small; lia).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
assert (M9 : (q + 8) mod 8 = 0) by (replace (q + 8) with (q + 1 * 8) by lia; rewrite Z_mod_plus_full; exact N4).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HS : st_ok tfibsegs (Ereg regs2 xs) ps2_ss0
  (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 0x85184) mem2 (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ss0. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_sr0.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E24 ltac:(lia)); exact R25].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rg0. constructor; [|constructor; [|constructor]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly2 S2 ps2_U2 W2 mem2 md2 _ HARU); [lia|]. apply Hpres. unfold ps2_STKw. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (q + 8) 0 8 (SOff 32 0) (text + len));
        [rewrite fsw_SOff0; exact EW32 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. apply ps2_in_end. intros y Hy. reflexivity.
  - unfold ps2_rg0. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9. repeat split; lia.
  - unfold ps2_fa0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E10, E20, E24, E32.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; first [exact M2 | exact Ham]
      | change (2 ^ 3) with 8; exact M9]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq [] (Ereg regs2 xs) (mrestrict (w_H W2) mem2)) by constructor.
change (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2)
  with (mkCfg (YK11.mkst regs2 (Z_to_bv 64 0x85184) mem2 (YK11.seg_rom tfibsegs)) md2).
(* run 1: to the `bgeu s4, a1` at 0x85198 *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85200.
{ unfold ps2_Bq. rewrite !U_SOff, E24, E9, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ (q + 8) 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) M9 eq_refl ltac:(lia)). }
{ apply (ps2_awr_wins _ _ [(2%nat, 8, 32)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. rewrite E2 in Hx. left; left. unfold ps2_STKw. lia. }
assert (HM0 : forall x : word, ~ (spZ regs - FRAME_PSTR + 8 <= bv_unsigned x < spZ regs - FRAME_PSTR + 32) ->
  mem2 x = mem2 x) by (intros; reflexivity).
pose proof (ps2_chainw _ _ _ _ _ 2 8 32 (spZ regs - FRAME_PSTR) HF ltac:(vm_compute; reflexivity) E2 HM0) as HM.
clear HF HFr HG HM0.
(* in->end is past the read cursor *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
{ exfalso. rewrite branch_geu_U, !U_SOff in Hc. ps2_ews_in Hc. rewrite E20, E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge in Hc. lia. }
clear Hc.
(* run 2: the constants, the three frame slots, s3 := a, to the loop head *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85200.
{ apply (ps2_awr_wins _ _ [(2%nat, 8, 32)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E2 in Hx. left; left. unfold ps2_STKw. lia. }
pose proof (ps2_chainw _ _ _ _ _ 2 8 32 (spZ regs - FRAME_PSTR) HF ltac:(vm_compute; reflexivity)
  ltac:(ps2_ews; exact E2) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
pose proof (@st_ok_restrict_mkst tfibsegs _ (w_H W2) _ _ _ HS eq_refl) as Hshape. rewrite Hshape.
rewrite ?wvb_collapse in HJ, HARU.
apply (ps2_loop (Z.to_nat (Q - 0)) 0); [reflexivity | lia |]. unfold ps2_LH.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj HJ (conj HARU (conj _ _)))))))))))))))))).
- apply ps2_spZ; [|lia]. apply (ps2_reg_val _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (spZ regs - FRAME_PSTR)); [ps2_ews; exact E2 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 3%bv 3 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R3.
- rewrite (ps2_reg_keep _ _ _ _ 4%bv 4 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R4.
- apply (ps2_reg_val _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ q); [ps2_ews; exact E8 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 9%bv (SOff 9 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (q + 8)); [ps2_ews; exact E9 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 18%bv (SOff 10 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E10 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 19%bv (SOff 10 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E10 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 20%bv (SOff 20 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (p + 1)); [ps2_ews; exact E20 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 23%bv 23 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R23.
- apply (ps2_reg_val _ _ _ _ 24%bv (SOff 24 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ SHADOW_OFF); [ps2_ews; exact E24 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 25%bv (ps2_shx 9) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E9 | ps2_ews; exact E24 | lia].
- apply (ps2_reg_val _ _ _ _ 26%bv (SLit 34) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 14%bv (SLit 32) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 16%bv (SLit 92) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_frame_keep W2 mem2); [lia | lia | | exact RF]. intros y Hy. apply HM. rewrite wz by lia. lia.
- intros x Hx1 Hx2. apply HM. lia.
- intros j Hj. lia.
Qed.

End L.

(* ---- the new block against the blocks of the entry (AR at the return) ---- *)
Lemma ps2_blocks : forall ly S ly2 S2 (W2 : world tfibsegs) mem2 md2 text tcap a Q,
  AR tfibsegs B ly2 S2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] ->
  In (text - HEAD, tcap + HEAD) (ablocks B ly S) -> 0 <= Q -> 0 < tcap ->
  ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S) /\
  (text + tcap <= a - HEAD \/ a + Q + 1 <= text - HEAD) /\
  a + Q + 1 <= alloc_ceiling /\ text + tcap <= alloc_ceiling /\
  (a + Q + 1 <= kLowShadowBeg \/ kHighMemBeg <= a - HEAD) /\
  (forall x, a - HEAD <= x < a + Q + 1 -> ~ in_img tfibsegs x).
Proof.
intros ly S ly2 S2 W2 mem2 md2 text tcap a Q HAR Hab HT HQ Htc.
pose proof (AR_laws_ok tfibsegs B) as LAWS. assert (EH : HEAD = 16) by reflexivity.
assert (HinA : In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HinT : In (text - HEAD, tcap + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; left; exact HT).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinA) as (_ & _ & Ca & Appa & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinT) as (_ & _ & Ct & _).
rewrite ps2_req in Ca, Appa by lia. rewrite ps2_req in Ct by lia.
assert (Hnew : ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S)).
{ intros Hin. apply in_split in Hin as (l1 & l2 & E).
  pose proof (sep_blocks_pos tfibsegs B LAWS _ _ _ _ _ (a - HEAD, Q + 1 + HEAD) (a - HEAD, Q + 1 + HEAD) l1 l2 [] HAR
    ltac:(rewrite Hab, E, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite ps2_req in Hd by lia. lia. }
split; [exact Hnew|].
split.
{ pose proof (sep_blocks tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR HinT HinA
    ltac:(intros Heq; apply Hnew; rewrite <- Heq; exact HT)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !ps2_req in Hd by lia. lia. }
split; [lia|]. split; [lia|].
split.
{ unfold in_app in Appa. destruct Appa as (_ & [H1 | (H1 & H2)]); [left; lia | right; lia]. }
intros x Hx. exact (blk_img tfibsegs B LAWS _ _ _ _ _ _ _ x HAR HinA ltac:(rewrite ps2_req by lia; lia)).
Qed.

Lemma pstr_stage2 : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt fail
    ly2 S2 W2 regs2 mem2 md2 a,
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  pstr_ret_facts B ly S U W regs mem md ot q p d Q text len tcap live peak cnt fail a tb ly2 S2 W2 regs2 mem2 md2 ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2)
    (fpostU tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP regs ly S U W mem md EV_fuzz_malloc
       (U ++ [(a - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          YK11.getr regs' 10 = w64 a /\ 4096 + HEAD <= a /\
          ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
          fs_rblock tfibsegs B ly' S' W' mem' a (Q + 1) /\
          PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a (run_at tb text p Q) /\
          PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Q + 2) d tb /\
          wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
          rd_text tfibsegs B ly' S' W' mem' text len tcap /\
          fs_glob tfibsegs W' mem' (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail)).
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail ly2 S2 W2 regs2 mem2 md2 a
  HPRE FH H10 HIN HWIN HTX Hp Hq Hrun HGL0 Hquiet HQm Hlive HRF.
destruct HRF as (Rsp & R10 & R3 & R4 & R8 & R9 & R20 & R23 & R24 & R25 & RF & HJ & HARU & HFH & Ha16 & Ham & Hab & HRB &
  HIN2 & HTX2 & HWK & HGL).
pose proof HPRE as ((HAP & _ & _) & _).
pose proof HAP as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (HSPal & _ & Hceil & HSTK & _ & H47 & _ & _ & Htophi).
pose proof HWIN as (Hq1 & Hq2 & _ & Hottop & _).
pose proof HTX as (_ & (HTX1 & _) & _).
pose proof HTX2 as (_ & (_ & _ & Htc & _) & _).
pose proof Hrun as (HQ0 & _).
pose proof HJ as (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo2 & Hhi2 & _).
pose proof (ps2_blocks ly S ly2 S2 W2 _ md2 text tcap a Q (proj1 HARU) Hab HTX1 HQ0 Htc)
  as (Hnew & Hdisj & Hca & Hct & Happ & Himg).
exact (ps2_r0 ly S U W regs mem md ot q text len p d tb tcap Q live peak cnt fail a ly2 S2 W2 mem2 Hra HSPal Hceil HSTK
  ltac:(lia) H47 Hq1 Hq2 Hlo2 Hhi2 HIN2 HTX2 HTX1 Hrun Hab Ha16 Ham HRB HFH HWK HGL Hnew Hdisj Hca Hct Happ Himg
  regs2 md2 Rsp R10 R3 R4 R8 R9 R20 R23 R24 R25 RF HJ HARU).
Qed.
End W2.

(* ================= the fuzz_malloc call 0x85180 and the composition =================
   pstr_call_step: from stage 1's call-site facts (pstr_call_facts) to stage 2's return-site facts (pstr_ret_facts):
   the chain moved to the call memory (pc_achain_agree), the callee's fpreU by FSW_ret's fsw_fpreU_atFP (the kit's
   FP-generic form, a Theorem Labs lane), fuzz_malloc_spec at n = Q + 1, and the journal
   composition by FSW_K3's fsw_rt_atU3 (its third FP arm: the four statics are image bytes, pc_fp_img).
   parse_string_proof_c5: stage 1, the call step, stage 2. Proved by a Theorem Labs lane in scratch; at the move to S0
   400b2a240b3 + hv5a its hand-applied afn_pre_at became fsw_fpreU_atFP. *)
Section W3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

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
(* FS_PSTAT_FP's four cells are image statics (in fs.asan's last loaded segment, ps2_img_hi) *)
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

(* ---- the fuzz_malloc call 0x85180: from stage 1's call-site facts to stage 2's return-site facts ---- *)
Lemma pstr_call_step : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt
    fail regsC memC mdC (Qp : world tfibsegs -> config -> Prop),
  fuzz_malloc_spec tfibsegs B ->
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs - FRAME_parse_string) q chq) ->
  spZ regs + 16 <= q ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb -> rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  st_nev S + EV_fuzz_malloc <= EV_MAX -> blocks_bytes S + (Q + 1 + HEAD) <= LIVE_MAX ->
  pstr_call_facts B ly S U W regs mem md ot q p Q regsC memC mdC ->
  (forall ly2 S2 W2 regs2 mem2 md2 a,
     pstr_ret_facts B ly S U W regs mem md ot q p d Q text len tcap live peak cnt fail a tb ly2 S2 W2 regs2 mem2 md2 ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_malloc regsC memC mdC) Qp.
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC Qp
  MALLOC HPRE FH [chq HCH] Hq16 H10 HIN HWIN HTX HPR HGL Hquiet HQm Hlive Hnev Hbb HCF HK.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & _ & K3 & _).
destruct HCF as (Csp & C1r & C10 & C3r & C4r & C8 & C9 & C20 & C23 & C24 & C25 & CM & CF & CJ & CARU).
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
assert (HSTK : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v)) by (vm_compute; reflexivity).
assert (HSTKm : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by (vm_compute; reflexivity).
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
(* 3. fuzz_malloc's contract at n = Q + 1 *)
assert (HGLc : fs_glob tfibsegs W memC live peak cnt fail) by exact (fs_glob_below W mem memC live peak cnt fail SB HGL).
eapply SRr_bind.
{ exact (MALLOC ly S U W regsC memC mdC chq (Q + 1) live peak cnt fail HPREc FH
    C10 ltac:(lia) HQm HGLc ltac:(lia) ltac:(lia)
    ltac:(unfold EV_fuzz_malloc in Hnev; exact Hnev) (fun _ => Hbb)). }
(* 4. the return *)
intros W' c' _ [(Hcf & _) | (_ & res & HPOST)].
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
split; [rewrite <- C23; exact (PR 23 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C24; exact (PR 24 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- C25; exact (PR 25 ltac:(unfold acallee_saved; lia))|].
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

(* ---- the composition: stage 1, the call step, stage 2 ---- *)
Theorem parse_string_proof : fuzz_malloc_spec tfibsegs B -> parse_string_spec tfibsegs B.
Proof.
intros MALLOC. unfold parse_string_spec.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail HPRE FH HEX Hq16 H10 HIN HWIN
  HTX Hp Hq Hrun HGL Hquiet HQm Hlive Hnev Hbb.
apply (pstr_stage1 B HSS ly S U W regs mem md ch q ot text len p d tb tcap Q _ HPRE FH H10 HIN HWIN HTX Hp Hq Hrun).
intros regsC memC mdC HCF.
apply (pstr_call_step ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail regsC memC mdC _
  MALLOC HPRE FH HEX Hq16 H10 HIN HWIN HTX Hrun HGL Hquiet HQm Hlive Hnev Hbb HCF).
intros ly2 S2 W2 regs2 mem2 md2 a HRF.
eapply SRr_mono.
{ exact (pstr_stage2 B (proj1 HSS) (proj2 HSS) ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail
    ly2 S2 W2 regs2 mem2 md2 a HPRE FH H10 HIN HWIN HTX Hp Hq Hrun HGL Hquiet HQm Hlive HRF). }
intros W' c' _ HPOST. exists a. exact HPOST.
Qed.
End W3.
