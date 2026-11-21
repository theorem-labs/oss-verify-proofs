(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; AT_EXECFN; the vDSO's mappings and steps; the channel-reader flag that fdchan asks for; the launch's channel-reader and SIGPIPE fields): changed MD0, MD_file, MD_dir, MD0_fds, MD0_fs, split_win, drv_lay, drv_state and 3 more; added reader_of_inp, MD0_rx_ok, MD0_vdso_incl, trim416, canon_mem, canon_state, ss_canon_t, ss_canon_f and 3 more. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03 YL07 YL01 YL08 YL0d YN2j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac at_node k :=
lazymatch goal with
| Hregs : regs_ok ?E ?sr _, Hmem : mem_ok _ _ _ ?rs, HG : facts_ok _ ?G
|- realizes _ (mkCfg (mkst (regupd _ 10 ?RET) (v_addi (Z_to_bv 64 ?pc) 4) _ _) _) _ =>
k E (mkSS pc sr rs (@None sv) G) RET
end.
Ltac resume_sv segs rv :=
at_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_sv segs E ss regs mem rv RET Hregs Hmem HG _) as H;
[ | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac resume_atom segs n f :=
at_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_atom segs n f E ss regs mem RET Hregs Hmem HG
ltac:(vm_compute; reflexivity) _ _ _) as H;
[ | | | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac drv_run_with tblok HS HF :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (rz_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (rz_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end.
Ltac drv_run_to_with tblok HS stop HF :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_to_ecall segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (rz_run_to_stop segs tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (rz_run_to_running segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end.
Ltac drv_runs E ss0 HS HF HR :=
lazymatch type of HS with
| st_ok ?segs _ ?ss' ?msn =>
eapply (runs_at_after segs E ss' msn (ss_mem ss0)) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
| st_ok_ecall ?segs _ ?ss' ?msn =>
eapply (runs_at_after_ecall segs E ss' msn (ss_mem ss0)) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
end.
Ltac drv_runs' E HS HF HR :=
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
lazymatch type of HS with
| st_ok ?segs _ ?ss' ?msn =>
eapply (runs_at_after segs E ss' msn rs0) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
| st_ok_ecall ?segs _ ?ss' ?msn =>
eapply (runs_at_after_ecall segs E ss' msn rs0) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
end end.
Ltac drv_anch := assumption.
Ltac drv_mr mraf keep E HS HF HMR :=
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
let G := lazymatch type of HS with st_ok _ _ ?ss' _ => constr:(ss_facts ss') | st_ok_ecall _ _ ?ss' _ => constr:(ss_facts ss') end in
let HG0 := fresh "HG0" in
assert (HG0 : facts_ok E G) by (lazymatch type of HS with
| st_ok _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X
| st_ok_ecall _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X end);
let HSA0 := fresh "HSA0" in
assert (HSA0 : stack_anchored E G) by drv_anch;
apply (mraf _ _ _ _ _ E G keep rs0 HMR HG0 HSA0 ltac:(vm_compute; reflexivity)) in HF;
clear HMR HG0 HSA0; rename HF into HMR
end.
Ltac model_facts M Hh Hlz :=
assert (Hh : m_halted M = None) by (autorewrite with model; reflexivity);
assert (Hlz : m_vm_lazy M = []) by (autorewrite with model; reflexivity).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma find_segment_above : forall (sl : list Segment) top a n,
forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sl = true ->
top <= a -> 0 < n -> find_segment sl a n = None.
Proof.
induction sl as [|sg rest IH]; intros top a n Hall Ha Hn; cbn [find_segment]; [reflexivity|].
cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply Z.leb_le in H1.
destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); cbn [andb];
[ destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [lia|] |];
eapply IH; eauto.
Qed.
Lemma seg_rom_above : forall segs top (a : word),
forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true ->
top <= bv_unsigned a -> seg_rom segs a = None.
Proof.
intros segs top a Hall Ha. unfold seg_rom, memory_read.
rewrite (find_segment_above segs top) by (try exact Hall; lia). reflexivity.
Qed.
Lemma src0_segs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x60000) src0segs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma runs_at_mbyte : forall spv m m' l,
0x60000 <= spv ->
(forall a, spv <= a -> a < 2 ^ 64 -> mbyte src0segs m' a = mbyte src0segs m a) ->
runs_at spv m l -> runs_at spv m' l.
Proof.
intros spv m m' l Hsp Hmb HR. unfold runs_at in *. rewrite Forall_forall in HR |- *.
intros [a bs] Hin. destruct (HR _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
split; [exact H1|]. split; [exact H2|]. intros j Hj.
specialize (H3 j Hj). specialize (Hmb (a + Z.of_nat j) ltac:(lia) ltac:(lia)).
unfold mbyte in Hmb.
rewrite (seg_rom_above src0segs 0x60000 _ src0_segs_top) in Hmb by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); rewrite Z.mod_small by lia; lia).
rewrite H3 in Hmb. destruct (m' (Z_to_bv 64 (a + Z.of_nat j))); destruct (nth_error bs j); cbn in Hmb; congruence.
Qed.
(* [Run.init_config] wraps the launch model in [with_vdso (vdso_run_init (ed_vdso draw))]
   (YN3e.src0_start), so the model the driver chain starts from carries the entry draw. *)
Definition MD0 (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved src0segs) brk mbase sp lim inp)).
Definition MD_file (path : list byte) (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp rnd)) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)))
(MD0 tid brk mbase sp lim inp rnd).
Definition MD_dir (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp rnd)) (Z_to_bv 64 3) FdDir) (MD0 tid brk mbase sp lim inp rnd).
Lemma MD0_fds : forall tid brk mbase sp lim inp rnd,
m_fds (MD0 tid brk mbase sp lim inp rnd) =
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Proof. intros. reflexivity. Qed.
Lemma MD0_fs : forall tid brk mbase sp lim inp rnd, m_fs (MD0 tid brk mbase sp lim inp rnd) = in_fs inp.
Proof. intros. reflexivity. Qed.
(* [fdchan] reads [m_channel_reader] at 727298f3, and [Run.valid_input] pins the launch's
   [in_channel_reader] to [true] (Run.v:4606); every model here carries it from [init_model]. *)
Lemma reader_of_inp : forall inp, valid_input inp -> in_channel_reader inp = true.
Proof. intros inp H. unfold valid_input in H. tauto. Qed.
(* The launch's reserved ledger is the image's reservations followed by the vDSO pair
   ([State.init_reserved]), the pair just below [min mbase (sp - stack_max_size)]
   ([State.vdso_top_init_model]); as [UL0k.MD0_rx_ok]. *)
Lemma MD0_rx_ok : forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk src0segs brk -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
rx_ok (bv_unsigned brk)
(vdso_reserved (in_kernel inp) (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))).
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hlau Hvi.
pose proof (entry_launch_ok_va_base Sv48 _ inp Hlau) as Hmb. cbn [en_mmap_base] in Hmb.
destruct Hmb as (M1 & M2 & _). destruct Hsp as (S1 & S2 & _). destruct Hbrk as (B1 & B2 & _).
assert (C : (reserved_top (segments_reserved src0segs) + brk_aslr_max + 2 ^ 20 + 24576 + 4096
<=? Z.min (va_mmap_base_min Sv48) (sp_window_lo - stack_max_size)) = true) by (vm_compute; reflexivity).
apply Z.leb_le in C.
assert (C2 : (va_mmap_base_max Sv48 <? 2 ^ 63) = true) by (vm_compute; reflexivity).
apply Z.ltb_lt in C2.
set (VT := page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
assert (HT : Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 4096 < VT
<= Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
{ unfold VT, page_round_down_Z, page_size. lia. }
assert (HK : vdso_reserved (in_kernel inp) VT = vdso_reserved default_kernel VT)
by exact (f_equal (fun k => vdso_reserved k VT) (valid_input_recorded_kernel inp Hvi)).
rewrite HK. unfold vdso_reserved. cbv zeta.
replace (vdso_len default_kernel) with 24576 by (vm_compute; reflexivity).
replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
replace (vdso_text_pages default_kernel * page_size)%Z with 8192 by (vm_compute; reflexivity).
assert (C3 : (0 <=? reserved_top (segments_reserved src0segs)) = true /\ (0 <=? brk_aslr_max) = true)
by (split; vm_compute; reflexivity).
destruct C3 as [C3 C4]. apply Z.leb_le in C3, C4.
replace (VT - 24576 <? page_size) with false by (symmetry; apply Z.ltb_ge; unfold page_size; lia).
unfold rx_ok. cbn [length YM01.ivs_bytes fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by lia.
split; [lia|]. split; [lia|].
apply Forall_forall. intros iv Hin. cbn [In] in Hin.
repeat destruct Hin as [Hin|Hin]; try contradiction; subst iv; cbn [fst];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia.
Qed.
Lemma MD0_vdso_incl : forall brk mbase sp lim inp md,
m_kernel md = in_kernel inp ->
m_vmmaps md = m_vmmaps (init_model (segments_reserved src0segs) brk mbase sp lim inp) ->
incl (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md))) (vm_reserved (m_vmmaps md)).
Proof.
intros brk mbase sp lim inp md Hk Hv. rewrite Hk, Hv, vdso_top_init_model.
change (vm_reserved (m_vmmaps (init_model (segments_reserved src0segs) brk mbase sp lim inp)))
with (init_reserved (segments_reserved src0segs) mbase sp (in_kernel inp)).
unfold init_reserved. apply incl_appr, incl_refl.
Qed.
Definition src0_keep : ivl := Eval vm_compute in (drv_keep src0_msyms).
Lemma src0_keep_check : keep_check src0_msyms src0_keep = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src0_errno_check : errno_check src0_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Definition RS_LO : Z := src0_D_read_stage.
Definition RS_HI : Z := src0_D_read_stage + 65536.
Definition TDCAN_LO : Z := src0_tp - 16.
Definition TDCAN_HI : Z := src0_tp - 8.
Definition cut_win (lo hi : Z) (x : nat * YP09.region) : nat * YP09.region :=
let r := snd x in
match r_base r with
| None => if (r_lo r <? hi) && (lo <? r_hi r) then (fst x, with_chunks r (cut_chunks lo hi (r_chunks r))) else x
| Some _ => x
end.
Definition split_win (lo hi : Z) (x : nat * YP09.region) : list (nat * YP09.region) :=
let r := snd x in
match r_base r with
| None => if (r_lo r <=? lo) && (hi <=? r_hi r)
then [ (fst x, carve r (r_lo r) lo (Z.max (r_wlo r) (r_lo r)) (Z.min (r_whi r) lo));
(fst x, YP09.mkRegion None lo hi 0 0 []);
(fst x, carve r hi (r_hi r) (Z.max (r_wlo r) hi) (Z.min (r_whi r) (r_hi r))) ]
else [x]
| Some _ => [x]
end.
(* [YN3e.ss_main] is indexed by the run's own rseq flag as well as by [two] (YN3e.v:96-98):
   the flag makes the entry stack's auxv block one pair longer.  The comment this replaces
   GUESSED that the four states collapse pairwise, and said -- correctly -- that the guess
   was NOT CHECKED BY A BUILD.  It is checked now and the guess was WRONG:
   a build of the old proof fails at its line 213 with
   "Unable to unify ss_main true true with ss_main false true".

   WHAT ACTUALLY DIFFERS, measured field by field by a probe (never merged):
   [ss_pc] is 76080 in all four states, [ss_resv] is None in all four, [ss_fregs] is empty,
   and [ss_regs] and [ss_facts] are BYTE-IDENTICAL between the rseq-on and rseq-off states.
   EXACTLY ONE REGION DIFFERS, the auxv block on atom 5: rseq-on (Some 5, 0..464, 50 chunks)
   against rseq-off (Some 5, 0..432, 46 chunks), the gap being four 8-byte chunks at offsets
   432, 440, 448 and 456.  464 = 29*16 and 432 = 27*16 -- the two extra auxv pairs
   CONFIG_RSEQ adds, and nothing else.

   SO THE rseq-OFF STATE IS THE WEAKER ONE AND THE IMPLICATION RUNS ONE WAY.  The rseq-off
   region is a [YP06.subregion] of the rseq-on one -- same base, 0 <= 0, 432 <= 464, its
   chunk list a prefix -- so [st_ok] of the rseq-ON state implies [st_ok] of the rseq-OFF
   state and NOT the converse.  The driver chain below is therefore computed from
   [ss_main false two], and [st_ok_main_rs] carries any [rs] to it.

   That is the SOUND direction, not a convenience.  [kb_rseq] is FREE under
   [Run.valid_input] (75d69e00:theories/LinuxProcessSem/Run.v:4596 fixes only the nine
   fields [recorded_kernel] copies), and [YN3e.src0_start] case-splits all four (rs, two)
   bullets explicitly (YN3e.v:613-620), so a chain that NEEDED the two extra pairs would be
   false for every rseq-off kernel.  Nothing is pinned here: [rs] stays universally
   quantified in the premise and no caller has to produce a flag.

   [YN2j.mergeb] is this unit's own decision procedure for exactly this implication -- pc,
   regs and resv equal, [submemb] of the memories, [facts_subb] of the facts -- and
   [YN2j.st_ok_merge] turns it into the [st_ok].  Ninety-five sites across both trees
   already use that pair; these are the ninety-sixth and ninety-seventh, not a new
   instrument. *)
(* MEASURED, not guessed.  A probe that decomposed [YN2j.mergeb]
   found exactly ONE false conjunct, [submemb], FALSE IN BOTH DIRECTIONS, at region
   index 4 of 12.  A second probe then decomposed [subregionb] at that
   region and printed the chunk VALUES: the two states DISAGREE IN VALUE at offsets
   416 and 424 -- rseq-off has [SLit 0; SLit 0], the AT_NULL terminator, where rseq-on
   has [SLit 27; SLit 28], the AT_RSEQ_* tag/value pair -- and rseq-on carries four
   further words at 432..456.  EVERY CHUNK BELOW 416 AGREES.

   So neither state is a submem of the other and there is no weakening between them in
   either direction.  The common weakening is region 4 TRUNCATED AT 416: it keeps only
   the chunks the two states agree on, and both are then above it.  [rs] stays
   universally quantified; nothing is pinned and no caller produces a flag. *)
(* r2: `The term "r_base r" has type "option nat" while it is
expected to have type "rkind"`. A NAME SHADOW, not a record-arity change: this file imports
YP09 (whose `Record region := mkRegion` leads with `r_base : option nat`) and then YO0i
(whose own `Record region := mkRegion` leads with its `Inductive rkind`), so later-import-wins
resolved the BARE `mkRegion` to YO0i's while every accessor here is YP09-qualified.
QUALIFIED rather than reordered: a qualified name cannot be shadowed, and reordering the
Require line would change what every other name in this file resolves to. *)
Definition trim416 (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) 416 (YP09.r_wlo r) (YP09.r_whi r)
(filter (fun c => Z.ltb (YP09.c_off c) 416) (YP09.r_chunks r)).
Definition canon_mem (m : YP09.smem) : YP09.smem :=
firstn 4 m ++ (match nth_error m 4 with Some r => [trim416 r] | None => [] end) ++ skipn 5 m.
Definition canon_state (two : bool) : sstate :=
mkSS (ss_pc (ss_main true two)) (ss_regs (ss_main true two)) (canon_mem (ss_mem (ss_main true two)))
(ss_resv (ss_main true two)) (ss_facts (ss_main true two)).
Definition ss_canon_t : sstate := Eval vm_compute in (canon_state true).
Definition ss_canon_f : sstate := Eval vm_compute in (canon_state false).
Definition ss_canon (two : bool) : sstate := if two then ss_canon_t else ss_canon_f.
Lemma st_ok_main_rs : forall rs two E ms,
st_ok src0segs E (ss_main rs two) ms -> st_ok src0segs E (ss_canon two) ms.
Proof.
intros [|] [|] E ms HS.
- exact (st_ok_merge src0segs E (ss_canon true) (ss_main true true) ms HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_merge src0segs E (ss_canon false) (ss_main true false) ms HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_merge src0segs E (ss_canon true) (ss_main false true) ms HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_merge src0segs E (ss_canon false) (ss_main false false) ms HS ltac:(vm_compute; reflexivity)).
Qed.
Definition drv_lay (two : bool) : list (nat * YP09.region) :=
map (cut_win TDCAN_LO TDCAN_HI) (flat_map (split_win RS_LO RS_HI) (drv_relayout src0_msyms (ss_mem (ss_canon two)))).
Definition drv_state (two : bool) : sstate :=
mkSS (ss_pc (ss_canon two)) (ss_regs (ss_canon two)) (map snd (drv_lay two)) (ss_resv (ss_canon two)) (ss_facts (ss_canon two)).
Definition ss_drv_t : sstate := Eval vm_compute in (drv_state true).
Definition ss_drv_f : sstate := Eval vm_compute in (drv_state false).
Definition ss_drv (two : bool) : sstate := if two then ss_drv_t else ss_drv_f.
Lemma st_ok_drv_canon : forall two E ms, st_ok src0segs E (ss_canon two) ms -> st_ok src0segs E (ss_drv two) ms.
Proof.
intros two E ms HS. destruct two.
- exact (st_ok_relayout src0segs E (ss_canon true) ms (drv_lay true) HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_relayout src0segs E (ss_canon false) ms (drv_lay false) HS ltac:(vm_compute; reflexivity)).
Qed.
Lemma st_ok_drv : forall rs two E ms, st_ok src0segs E (ss_main rs two) ms -> st_ok src0segs E (ss_drv two) ms.
Proof.
intros rs two E ms HS. apply (st_ok_main_rs rs two) in HS. exact (st_ok_drv_canon two E ms HS).
Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition ss_open : sstate := Eval vm_compute in (run_ (add_cond ss_drv_t (mkAC BC_EQ (SOff 3 0) (SLit 2)))).
Definition ss_m1 : sstate := Eval vm_compute in
(runto_ src0_A_malloc (resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open))).
Definition MAIN_SP : Z := -128.
Definition K_M1 : nat := 10.
Definition A_BUF : nat := 14.
Definition G_M1 : nat := 26.
Definition L_m1 : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem ss_m1)).
Definition RS_m1 : smem := Eval vm_compute in
(match drv_add_statics src0_msyms (map snd L_m1) G_M1 with Some x => x | None => [] end).
Definition RA_m1 : Z := Eval vm_compute in (src0_A_main + 0x54).
Lemma site_m1 : site_check src0_msyms ss_m1 src0_A_malloc RA_m1 MAIN_SP src0_keep [] K_M1 L_m1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_m1 : drv_add_statics src0_msyms (map snd L_m1) (K_M1 + 16) = Some RS_m1.
Proof. vm_compute. reflexivity. Qed.
Lemma pristine_m1 : pristine_check src0_msyms (ss_mem ss_m1) = true.
Proof. vm_compute. reflexivity. Qed.
(* [ss_m1] holds for both CONFIG_RSEQ flags (the auxv block is cut at 416, [trim416]), so it
   checks the 26 shared pairs; the flag's keys from pair 26 on come from [YN3e.runs_main]. *)
Lemma auxv_m1 : auxv_check_head src0_msyms (ss_mem ss_m1) (ss_facts ss_m1) 5 6 = true.
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_post : sstate := Eval vm_compute in (post_state ss_m1 RA_m1 K_M1 RS_m1).
Definition ss_m1_null : sstate := Eval vm_compute in
(mkSS (ss_pc ss_m1_post) (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0)) (ss_mem ss_m1_post) (ss_resv ss_m1_post) (ss_facts ss_m1_post)).
(* [E_main] gained [inp] and [efn] (YN3e.v:69-71); [efn] is [in_execfn inp] at every call
   site in this tree, so it is read off [inp] here rather than passed. *)
Definition E_m1 (sp tid : word) (inp : ProcInput) (argv envp : list (list byte)) (rnd : EntryDraw) (regs' : bvmap 5 word) (g : Z) : env :=
post_env (E_main sp inp argv envp (in_execfn inp) tid rnd) K_M1 regs' g.
Definition blk_fact : afact := mkAF 4096 CEIL_MAX 4.
Definition ss_m1_ok : sstate := Eval vm_compute in (add_atom ss_m1_post A_BUF blk_fact).
Definition ss_rd1 : sstate := Eval vm_compute in (run_ ss_m1_ok).
Definition ss_rderr : sstate := Eval vm_compute in (resume ss_rd1 (SLit (2 ^ 64 - 21)) (ss_mem ss_rd1) (ss_facts ss_rd1)).
Lemma ss_rd1_facts :
ss_pc ss_rd1 = src0_A_syscall_cp_c + 0x1c /\ sr_get (ss_regs ss_rd1) 17%bv = SLit 63 /\ sr_get (ss_regs ss_rd1) 10%bv = SLit 3 /\
sr_get (ss_regs ss_rd1) 11%bv = SLit RS_LO /\ sr_get (ss_regs ss_rd1) 12%bv = SLit 65536 /\ ss_resv ss_rd1 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma stations_pc : ss_pc ss_m1 = src0_A_malloc /\ ss_pc ss_m1_post = RA_m1.
Proof. vm_compute. split; reflexivity. Qed.
End b.
