(* fs program part, READER group, image B (fs.asan-ubsan): the SHARED definitions of the ASan walk of parse_string
   (A_parse_string 0x85534, pf.c:117-181), PLAIN-BYTE CASE. Stage 1 and the fuzz_malloc call step
   (lib/B/FSW_parse_string.v) and stage 2 (lib/B/FSW_parse_string_s2.v) Require this file; neither restates what is
   here.
   rule 24: proves no function (kind: walk definitions; the walk's rule-24 line is in lib/B/FSW_parse_string.v).

   TEMPLATES. The definitions and lemma names are image A's walk, a working branch 9f3343583b7
   lib/A/FSW_parse_string.v :89-115 (addresses, frame, Section W), :117-162 (pstr_frame_at, pstr_call_facts,
   pstr_ret_facts), :163-264 (the shadow lemmas), :372-445 (memory and register readers), :705-720 (pstr_shx),
   :1146-1147 (ps2_req) and :1259-1267 (ps2_img_hi). The B values are read off the B listing (a Theorem Labs lane's
   parse_string.B.s, 386 four-byte instructions 0x85534 .. 0x85b3c) and checked against the bespoke B proof,
   a working branch 955803f9b2e lib/B/Prog/parse_string_segs.v :39-47 (aps_out: s0 = q, s1 = q + 8,
   s6 = q >> 3 + K, s7 = K, s8 = (q + 8) >> 3 + K) and lib/B/Prog/parse_string.v :1180 (aps_some, the Some-Q path).

   WHAT IS B's (not A's):
   - the call `jal fuzz_malloc` is at 0x85614, so the return address is 0x85618 (A 0x85184); the scan loop head is
     0x855c8 (A 0x8513c); the `ret` is 0x85a5c (A 0x855fc).
   - the shadow base is in s7 (x23; A s8 = x24), loaded through the GOT word 0x9fc10 (0x85578 `auipc a0,0x1a` +
     0x8557c `ld a0,0x698(a0)` + 0x85580 `ld s7,0(a0)`); the shadow cell of in->p is s6 = x22 (A s7 = x23,
     0x85584-0x85588), the shadow cell of in->end is s8 = x24 (A s9 = x25, 0x855a8-0x855ac).
   - s0 = q (0x8556c `mv s0, a0`), s1 = q + 8 (0x855a4), s4 = x20 = in->p + 1 (0x85594-0x85598): as A.
   - the prologue's frame (0x90 = FSH_Base.FRAME_parse_string) and the 13 saved words (ra at 0x88 down to s11 at
     0x28, listing 0x85538 .. 0x85568) are A's.
   - FsShadowSyms is B's (FSH_Base.v: the GOT word 0x9fc10 = YB1w.tfib_D_GOT_asan_shadow_memory_dynamic_address and
     the cell 0xa8438 = YB1w.tfib_D_asan_shadow_memory_dynamic_address), the form the kit's entry and return states
     take (lib/B/FSW_K.v fsw_entryT_args).
   - the last loaded segment of fs.asan-ubsan is [0xa1000, 0x5fd000) as in A (lib/B/YD1y.v:65-73
     AsanUbsan_segment_003); FS_PSTAT_FP's four cells (lib/B/FSPstat.v) lie in it.
   No Admitted, no Axiom, no Parameter, no admit. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
Import ListNotations.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the addresses of the walk (FSH_Base.A_parse_string and the B listing) ---- *)
Definition RA_PSTR_MALLOC : Z := 0x85618.      (* after `jal fuzz_malloc` 0x85614 *)
Definition PSTR_SCAN : Z := 0x855c8.           (* the scan loop head *)
Definition PSTR_RET : Z := 0x85a5c.            (* the `ret` *)
(* the prologue's frame, 0x90: FSH_Base names it, this file never restates the numeral *)
Definition FRAME_PSTR : Z := FRAME_parse_string.
(* the 13 callee-saved words the prologue writes, as (offset in the frame, register number): ra at 0x88 down to
   s11 at 0x28 (listing 0x85538 .. 0x85568) *)
Definition pstr_saved : list (Z * Z) :=
  [(0x88, 1); (0x80, 8); (0x78, 9); (0x70, 18); (0x68, 19); (0x60, 20); (0x58, 21); (0x50, 22); (0x48, 23);
   (0x40, 24); (0x38, 25); (0x30, 26); (0x28, 27)].

(* concrete bounds the symbolic engine's range reasoning uses: the caller's struct pj_in is on the real stack
   ([2 ^ 46, 2 ^ 47]), the text block is application memory below alloc_ceiling (asan_consts) *)
Definition RQLO : Z := 2 ^ 46.
Definition RQHI : Z := 2 ^ 47 - 24.
Definition RTLO : Z := 4096.
Definition RTHI : Z := 0x7fffff800000.

(* the env of a symbolic state, named *)
Tactic Notation "pstr_env" constr(HS) ident(nm) :=
  lazymatch type of HS with st_ok _ ?Ev _ _ => pose (nm := Ev) end.

(* every walk file declares this Section context: Section <name>. Context {fx : YK11.FPState} {rc : YM05.RunCeil}
   {SK : YI16.sink_head}. Variable B : asyms. Hypothesis HSS : FsShadowSyms B. (the shadow-cell pair the kit's entry
   and return states need: Let TL_got := proj1 HSS, Let TL_cell := proj2 HSS below). The definitions and lemmas of
   this file use no HSS, so after End W they take B (and fx / rc / SK) only. *)
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Let TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

(* ---- the two interfaces the stages meet at: the state at the fuzz_malloc call 0x85614 (stage 1's conclusion,
   what the call step consumes: the caller journal, the ARU, the resumed sp and the frame words) and the state at
   its return 0x85618 (stage 2's premise, what the call step and FSH_Fn_alloc.fuzz_malloc_spec give back).
   B's registers there: s0 (8) = q, s1 (9) = q + 8, s4 (20) = in->p + 1, s6 (22) = SHADOW_OFF + q / 8,
   s7 (23) = SHADOW_OFF, s8 (24) = SHADOW_OFF + (q + 8) / 8, gp (3) / tp (4) the entry's ---- *)
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
  YK11.getr regsC 22 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regsC 23 = w64 SHADOW_OFF /\
  YK11.getr regsC 24 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  (forall x : word, ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) -> memC x = mem x) /\
  pstr_frame_at W memC regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U memC) mdC 0 /\
  ARU tfibsegs B ly S U W memC mdC.
(* at the return 0x85618: fuzz_malloc's block (a - HEAD, Q + 1 + HEAD) is live and its head is the appended U entry,
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
  YK11.getr regs2 22 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regs2 23 = w64 SHADOW_OFF /\
  YK11.getr regs2 24 = w64 (SHADOW_OFF + (q + 8) / 8) /\
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

(* ---- the stack's shadow reads 0 (lib/A/ACex.v:322-339 stack_cells8 / RA_stack, restated as image A's walk does) ---- *)
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
(* ---- a run whose regions all have an empty write window leaves the memory alone ---- *)
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

(* the shadow address of an object, as the code computes it (lib/A/ACep.v:203-213 denot_shx, restated as image A's
   walk does) *)
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
End W.

(* ---- the size fuzz_malloc's block reserves, and the image segment of alloc.c's statics: shared by stage 2 and the
   call step ---- *)
Lemma ps2_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
(* the last loaded segment of fs.asan-ubsan, [0xa1000, 0x5fd000) (lib/B/YD1y.v:65-73 AsanUbsan_segment_003), holds
   fuzz/alloc.c's statics *)
Lemma ps2_img_hi : forall x, 0xa1000 <= x < 0x5fd000 -> in_img tfibsegs x.
Proof.
intros x Hx.
assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) =? 659456) && (Z.of_N (seg_size sg) =? 5619712)) tfibsegs = true)
  by (vm_compute; reflexivity).
apply existsb_exists in Hb as (sg & Hin & Hsg). apply andb_prop in Hsg as [H1 H2]. apply Z.eqb_eq in H1, H2.
exists sg. split; [exact Hin | lia].
Qed.
