From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the ASan-image walk of musl fmemopen for
   libreac/fuzz_pcap v1.9.0 -- the proof of lib/A/Stdio/PFmemopenM.v's rfmemopen_contract at the musl
   entry 0x8e870 (PFMEMOPEN), with ra = 0x8e90c (FM_MALLOC_RA) and the __strchrnul window
   [0x10350, 0x10370).

   PORTED from proofs/libreac/fuzz_pcap/lib/Prog/fmemopen_c.v, fmemopen_pro.v and fmemopen_tail.v (the
   released PLAIN proof of the same 116 instructions): the case split and the pcs only, restated in the
   core's ASan vocabulary. The PLAIN files are not imported (lib/Lib's mkst empties the FP state).

   THE WALK (fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record) lines 99107-99223, and __ofl_add / __ofl_lock / __ofl_unlock /
   __lock / __unlock), six symbolic runs and three callee contracts:
     A  0x8e870 .. jal strchr 0x8e8a0            frame of 48, ra s0..s4 saved; strchr(mode, '+')
        tfib_strchr_lit (A/AE2j.v) at 0x41568   -> 0
     B  0x8e8a4 .. jal strchr 0x8e8b4            mode[0] = 'r' read; strchr("rwa", 'r')
        tfib_strchr_lit                          -> "rwa" (0x20026)
     C  0x8e8b8 .. jal malloc 0x8e908            beqz a0 not taken ("rwa" <> 0); bnez s1 TAKEN (b >= 4096)
        amalloc04_rule (the contract's own hypothesis) through PaJournalFs.amalloc04_sub_fs
     D  0x8e90c .. jal memset 0x8e92c            bnez a0 TAKEN: the malloc NULL branch 0x8e910 is refuted
                                                 by amalloc04_rule's 4096 <= res (YC5d.v:72), the route
                                                 through the rule; no refusal fact is re-derived
        aintrin_realizes OSet at 0x5150c (AINTR) through YC85G.aj_intrin_atS
     E  0x8e930 .. 0x8f23c                       the FILE set-up stores, the epilogue, the tail jump into
                                                 __ofl_add, __ofl_lock / __lock (need_locks = 0) and the
                                                 store f->next = old head (0)
     F  0x8f23c .. ret 0x8f254                   the head store (the only image byte written), __ofl_unlock
                                                 / __unlock (lock word 0), __ofl_add's epilogue and ret
   Runs A-D carry the journal through YCbq.SRr_run_AJ and run E through SRr_run_to_AJ (stack + the fresh
   FILE block). Run F writes the
   open-file list head, which awr_byte has no case for, so it is run plainly (YA0o.SRr_run_gen) and the
   journal is rebuilt by fm_head_journal (WFclose.v's wf_frameW / wf_journal_write, for the head alone).

   THE FOUR UNTAKEN ZERO RETURNS: 0x8e8b8 (strchr NULL) is excluded by tfib_strchr_lit's result for "rwa";
   0x8e8bc/0x8e8c0 (buf NULL, size sign) by b >= 4096; 0x8e910 (malloc NULL) by 4096 <= res. No path of
   the walk reaches an __asan_report_* or CheckFailed entry: every function stepped here is uninstrumented
   musl, and the three interceptor calls are taken as contracts.

   SECTION HYPOTHESES (named; no axiom, no Admitted):
     ASIL    asource_img_laws SK tfibsegs B pcap_KS   -- a Theorem Labs lane's PSourceMeta.v; discharged once against
                                                         a Theorem Labs lane's B (PSourceK.v:48-52)
     TL      PcapSyms B (A/AF0m.v, gated PASS A+B)    -- a Theorem Labs lane's B (A/AD2l.v PcapB_syms at B := PcapB)
     AINTR   aintrin_realizes tfibsegs B OSet 0x5150c  -- the ASan memset interceptor; the core's (a Theorem Labs lane)
                                                         A/AE32.v memset_icpt_realizes states it, but AE32
                                                         does not build at a working branch e8bb946b7e4 (A/AE79.v:
                                                         `pcap_img_end` not found)
   The strchr calls use a Theorem Labs lane's PROVED contract tfib_strchr_lit (lib/A/AE2j.v, a working branch
   2bf40e72137), whose premises cells_hold st_cells / rwa_img / mconsts_view this walk discharges from AR + TL,
   asrc_stdio_env and rfmemopen_pre's window [0x10350, 0x10370).
   Values consumed from a working branch's gen/A (WIP): AF0m Tfib_const_abs rows 0x9b540 -> 0x93058 and
   0x20d43..0x20d47 = 0, Tfib_const_shadow rows 0x7fffc1a8..ab, Tfib_zero_shadow rows (0x10000, ..) and
   (0x20d60, ..), PcapSyms' ts_code / ts_zsh; AF0x tfib_const_lookup; AE2y const_chk; AE2h cells_hold. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YC20 YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG0q YG0s YG0v YG0p YP08.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0l AF0m AF0x AE2y AE2h AE39 AE2j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require YC85G YC4b PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK PFmemopenM.
(* PFMEMOPEN / FM_MALLOC_RA come from PStdioImgA, the single home of pcap's asan stdio pcs (a Theorem Labs lane
   02:44Z). Imported LAST so its definitions are the ones in scope; this file declares neither locally. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PStdioImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* lib/A/AE2f.v sets this flag to false globally; restore lia's div / mod handling in this file. The
   redefinition is LOCAL to this file: it does not escape the Require, so a file that Requires this one
   keeps its own setting. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. Addresses, all MEASURED on fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record).     *)
(* ---------------------------------------------------------------------------------------------- *)
Definition FM_STRCHR : Z := (symaddr Symbols.Asan.s___wrap_strchr).   (* __interceptor_trampoline_strchr, target of 0x8e8a0 / 0x8e8b4 *)
Definition FM_RA1    : Z := (symaddr (Symbols.Asan.s_fmemopen + 0x34)%Z).   (* after the first strchr call *)
Definition FM_RA2    : Z := (symaddr (Symbols.Asan.s_fmemopen + 0x48)%Z).   (* after the second strchr call *)
Definition FM_MALLOC : Z := (symaddr Symbols.Asan.s___wrap_malloc).   (* __interceptor_trampoline_malloc, target of 0x8e908 *)
Definition FM_MEMSET : Z := (symaddr Symbols.Asan.s___wrap_memset).   (* __interceptor_trampoline_memset, target of 0x8e92c *)
Definition FM_RA4    : Z := (symaddr (Symbols.Asan.s_fmemopen + 0xc0)%Z).   (* after the memset call *)
Definition FM_HEADST : Z := (symaddr (Symbols.Asan.s___ofl_add + 0x24)%Z).   (* __ofl_add's `sd s0,0(a0)`, the head store *)
Definition FM_MODE   : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z).   (* "rb\0" = as_mode pcap_KS *)
Definition FM_RWA    : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 0xfd46)%Z).   (* "rwa\0" = as_rwa pcap_KS *)
Definition FM_THR    : Z := (symaddr (Symbols.Asan.s___libc + 0x1)%Z).  (* __libc+1 = as_threaded pcap_KS *)
Definition FM_NL     : Z := (symaddr (Symbols.Asan.s___libc + 0x3)%Z).  (* __libc+3 = as_need_locks pcap_KS *)
Definition FM_LOCK   : Z := (symaddr Symbols.Asan.s_ofl_lock).  (* ofl_lock *)
Definition FM_HEAD   : Z := (symaddr Symbols.Asan.s_ofl_head).  (* ofl_head *)
Definition FM_MC_LO  : Z := AE39.MC_LO.  (* __strchrnul's constants, A/AE39.v MC_LO *)
Definition FM_MC_HI  : Z := AE39.MC_HI.  (* A/AE39.v MC_HI *)
Lemma FM_MC_vals : FM_MC_LO = (symaddr (Symbols.Asan.Sec.s_rodata + 0x70)%Z) /\ FM_MC_HI = (symaddr (Symbols.Asan.Sec.s_rodata + 0x90)%Z).
Proof. vm_compute. split; reflexivity. Qed.
Definition FPT : list (Z * Z) := [YI16.sink_token].

(* ---------------------------------------------------------------------------------------------- *)
(* 2. The code table: fmemopen (116 words) and the musl functions the tail reaches.                *)
(* ---------------------------------------------------------------------------------------------- *)
Definition fm_ranges : list (Z * nat) :=
  [ (PFMEMOPEN, 116%nat); ((symaddr Symbols.Asan.s___ofl_lock), 12%nat); ((symaddr Symbols.Asan.s___ofl_unlock), 3%nat); ((symaddr Symbols.Asan.s___ofl_add), 16%nat);
    ((symaddr Symbols.Asan.s___lock), 162%nat); ((symaddr Symbols.Asan.s___unlock), 29%nat) ].
Fixpoint fm_build (rs : list (Z * nat)) (t : ctable) : ctable :=
  match rs with [] => t | (lo, n) :: rest => fm_build rest (build_table tfibsegs lo n t) end.
Lemma fm_build_ok : forall rs t,
  Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (fm_build rs t).
Proof.
  induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
  inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition fm_tbl : ctable := Eval vm_compute in fm_build fm_ranges TEmpty.
Lemma fm_tbl_eq : fm_tbl = fm_build fm_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl fm_tbl). Qed.
Lemma fm_tbl_ok : table_ok tfibsegs fm_tbl.
Proof.
  rewrite fm_tbl_eq. apply fm_build_ok; [| apply table_ok_empty].
  unfold fm_ranges. repeat constructor; cbn; discriminate.
Qed.
(* The table stops at the three trampolines (the callee contracts take over there). *)
Lemma fm_tbl_probe :
  clookup fm_tbl PFMEMOPEN = Some 0xfd010113 /\ clookup fm_tbl (symaddr (Symbols.Asan.s___ofl_add + 0x3c)%Z) = Some 0x00008067 /\
  clookup fm_tbl FM_STRCHR = None /\ clookup fm_tbl FM_MALLOC = None /\ clookup fm_tbl FM_MEMSET = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fm_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hlo & Hhi).
  assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))
                 tfibsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb sg Hin).
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.
Lemma fm_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 3. The symbolic states and their runs (all by vm_compute).                                      *)
(* ---------------------------------------------------------------------------------------------- *)
Definition fm_RUN (s : sstate) : sstate * run_status := sym_runN tfibsegs fm_tbl FUEL s.
Definition fm_RUNTO (stop : Z) (s : sstate) : sstate * run_status := sym_run_toN tfibsegs fm_tbl FUEL stop s.
Definition ck (o : Z) (n : N) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal n v).

(* A: the entry; a2 = the "rb" literal. *)
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition ssA : sstate := mkSS PFMEMOPEN (sr_set sr_atoms 12%bv (SLit FM_MODE)) [stkA] None
  (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition eA : sstate := Eval vm_compute in fst (fm_RUN ssA).
Lemma r_A : fm_RUN ssA = (eA, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* B: strchr(mode, '+') returned 0; s3 = the "rb" literal. *)
Definition modeR : YP09.region := YP09.mkRegion None FM_MODE (FM_MODE + 3) 0 0 [ck FM_MODE 1 (SLit 114)].
Definition ssB : sstate := mkSS FM_RA1 (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 19%bv (SLit FM_MODE)) [modeR] None
  (mkFacts [] [] []).
Definition eB : sstate := Eval vm_compute in fst (fm_RUN ssB).
Lemma r_B : fm_RUN ssB = (eB, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* C: strchr("rwa", 'r') returned "rwa"; s1 = b >= 4096. *)
Definition ssC : sstate := mkSS FM_RA2 (sr_set sr_atoms 10%bv (SLit FM_RWA)) [] None
  (mkFacts [(9%nat, mkAF 4096 (2^47) 0)] [] []).
Definition eC : sstate := Eval vm_compute in fst (fm_RUN ssC).
Lemma r_C : fm_RUN ssC = (eC, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* D: malloc returned res >= 4096, 16-aligned. *)
Definition ssD : sstate := mkSS FM_MALLOC_RA sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2^47) 4)] [] []).
Definition eD : sstate := Eval vm_compute in fst (fm_RUN ssD).
Lemma r_D : fm_RUN ssD = (eD, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* E: memset(res, 0, 272) returned; the frame words are the extra atoms 32..37 (s4 s3 s2 s1 s0 ra). *)
Definition stkE : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 48
  [ck 0 8 (SOff 32 0); ck 8 8 (SOff 33 0); ck 16 8 (SOff 34 0); ck 24 8 (SOff 35 0); ck 32 8 (SOff 36 0);
   ck 40 8 (SOff 37 0)].
Definition fileE : YP09.region := YP09.mkRegion (Some 8%nat) 0 272 0 272 [YP09.mkChunk 0 (CZero 272)].
Definition thrR : YP09.region := YP09.mkRegion None FM_THR (FM_THR + 1) 0 0 [ck FM_THR 1 (SLit 0)].
Definition nlR : YP09.region := YP09.mkRegion None FM_NL (FM_NL + 1) 0 0 [ck FM_NL 1 (SLit 0)].
Definition headR : YP09.region := YP09.mkRegion None FM_HEAD (FM_HEAD + 8) 0 0 [ck FM_HEAD 8 (SLit 0)].
Definition ssE : sstate := mkSS FM_RA4 (sr_set (sr_set sr_atoms 19%bv (SLit FM_MODE)) 20%bv (SLit 0))
  [stkE; fileE; modeR; thrR; nlR; headR] None
  (mkFacts [(2%nat, mkAF (2^44) (2^47) 4); (8%nat, mkAF 4096 (2^47) 4); (9%nat, mkAF 4096 (2^47) 0)] [] []).
Definition eE : sstate := Eval vm_compute in fst (fm_RUNTO FM_HEADST ssE).
Lemma r_E : fm_RUNTO FM_HEADST ssE = (eE, RS_running). Proof. vm_compute. reflexivity. Qed.

(* F: the head store and the rest; atoms 32 / 33 are the entry s0 / ra saved by __ofl_add. *)
Definition stkF : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [ck 0 8 (SOff 32 0); ck 8 8 (SOff 33 0)].
Definition headW : YP09.region := YP09.mkRegion None FM_HEAD (FM_HEAD + 8) FM_HEAD (FM_HEAD + 8) [].
Definition lockR : YP09.region := YP09.mkRegion None FM_LOCK (FM_LOCK + 4) 0 0 [ck FM_LOCK 4 (SLit 0)].
Definition ssF : sstate := mkSS FM_HEADST (sr_set sr_atoms 10%bv (SLit FM_HEAD)) [stkF; headW; lockR] None
  (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition eF : sstate := Eval vm_compute in fst (fm_RUN ssF).
Lemma r_F : fm_RUN ssF = (eF, RS_stopped (SR_jalr (SOff 33 0))). Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 4. Generic helpers over tfibsegs (after WFflush.v's and WFclose.v's, for this walk).            *)
(* ---------------------------------------------------------------------------------------------- *)
Definition chunk_at (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
  match nth_error (ss_mem ss) i with
  | Some r => existsb (fun c => (YP09.c_off c =? off) &&
                match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end) (YP09.r_chunks r)
  | None => false
  end.
Definition zchunk_at (ss : sstate) (i : nat) (off len : Z) : bool :=
  match nth_error (ss_mem ss) i with
  | Some r => existsb (fun c => (YP09.c_off c =? off) &&
                match YP09.c_val c with CZero l => l =? len | _ => false end) (YP09.r_chunks r)
  | None => false
  end.
Definition rbase_at (ss : sstate) (i : nat) : option nat :=
  match nth_error (ss_mem ss) i with Some r => YP09.r_base r | None => None end.

Section H. Context {fx : YK11.FPState}.

Lemma fm_chunk_val : forall E ss (H : word -> bool) ms i off n v bn,
  st_ok tfibsegs E ss (restrict H ms) -> chunk_at ss i off n v = true -> rbase_at ss i = Some bn -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E bn) + off) (N.to_nat n)
    (bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E ss H ms i off n v bn HS Hc Hb Hn.
unfold chunk_at, rbase_at in *. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
apply existsb_exists in Hc as ([o cv] & Hin & Hck). cbn [YP09.c_off YP09.c_val] in Hck.
apply andb_prop in Hck as [Ho Hcv]. apply Z.eqb_eq in Ho. subst o.
destruct cv as [n' e|l0|l0|d0 s0 l0]; try discriminate. apply andb_prop in Hcv as [Hn' He].
apply N.eqb_eq in Hn'. apply sv_eqb_eq in He. subst n' e.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
exact (YC4b.val_of_chunk_any tfibsegs E _ _ off n v Hck Hn).
Qed.

Lemma fm_zchunk_val : forall E ss (H : word -> bool) ms i off len bn o (n : nat),
  st_ok tfibsegs E ss (restrict H ms) -> zchunk_at ss i off len = true -> rbase_at ss i = Some bn ->
  off <= o -> o + Z.of_nat n <= off + len ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E bn) + o) n 0.
Proof.
intros E ss H ms i off len bn o n HS Hc Hb Ho1 Ho2.
unfold zchunk_at, rbase_at in *. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
apply existsb_exists in Hc as ([o' cv] & Hin & Hck). cbn [YP09.c_off YP09.c_val] in Hck.
apply andb_prop in Hck as [Ho Hcv]. apply Z.eqb_eq in Ho. subst o'.
destruct cv as [n' e|l0|l0|d0 s0 l0]; try discriminate. apply Z.eqb_eq in Hcv. subst l0.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
intros k Hk.
destruct (Hck (o - off + Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (bt & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (bv_unsigned (ew E bn) + o + Z.of_nat k) with (bv_unsigned (ew E bn) + off + (o - off + Z.of_nat k)) by lia.
change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)).
rewrite Hb2. f_equal. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma fm_garr8_byte : forall m base l j, garr8 tfibsegs m base l -> (j < length l)%nat ->
  mbyte tfibsegs m (base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)).
Proof.
intros m base l j H Hj. destruct (H j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. rewrite Hv. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma fm_vm_fr : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma fm_vm_eq : forall m a (n : nat) v v', val_mem tfibsegs m a n v -> v = v' -> val_mem tfibsegs m a n v'.
Proof. intros m a n v v' H ->. exact H. Qed.

Lemma fm_mb_frame : forall E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma fm_nwr_all : forall E rs a,
  Forall (fun r : YP09.region => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
  ~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). exact (proj1 (Forall_forall _ _) HF r Hin Hr). Qed.

Lemma fm_reg_of : forall E ss (H : word -> bool) ms (r : bv 5) v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> getr (ms_regs ms) r = sv_denot E v.
Proof. intros E ss H ms r v HS Hv. rewrite <- Hv. exact (st_ok_reg tfibsegs E ss (restrict H ms) r HS). Qed.

Lemma fm_reg_kept : forall E ss (H : word -> bool) ms regs0 extra (r : Z),
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> 0 <= r < 32 ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss H ms regs0 extra r HS HE Hr Hv. rewrite (fm_reg_of E ss H ms _ _ HS Hv). subst E.
cbn [sv_denot]. rewrite Z.add_0_r, ew_Ereg_lt by lia. rewrite Z2Nat.id by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* An atom read back as a 64-bit value. *)
Lemma fm_soff0 : forall E n (w : word), ew E n = w ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = bv_unsigned w.
Proof.
intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply Z.mod_small.
pose proof (u64_range w). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
Qed.

Lemma fm_aview_mod : forall H (m : word -> option byte) a,
  aview tfibsegs H m a = aview tfibsegs H m (a mod 2 ^ 64).
Proof.
intros H m a. assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
unfold aview, mbyte. rewrite E. reflexivity.
Qed.

End H.

Definition fm_keep (r0 r1 : bvmap 5 word) : Prop :=
  forall r, In r [3; 4; 21; 22; 23; 24; 25; 26; 27] -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Lemma fm_keep_trans : forall r0 r1 r2, fm_keep r0 r1 -> fm_keep r1 r2 -> fm_keep r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma fm_keep_pres : forall r0 r1, aregs_preserved r0 r1 -> fm_keep r0 r1.
Proof. intros r0 r1 H r Hr. apply H. unfold acallee_saved. cbn [In] in Hr. lia. Qed.
Lemma fm_keep_kepts : forall r0 r1,
  (forall r, In r KEPTS -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) -> fm_keep r0 r1.
Proof. intros r0 r1 H r Hr. apply H. unfold KEPTS. cbn [In] in Hr |- *. tauto. Qed.

(* The six words fmemopen saves at entry: s4 s3 s2 s1 s0 ra at sp0-48 .. sp0-8. *)
Definition fm_frame (sp0 : Z) (m : word -> option byte) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs m (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem tfibsegs m (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (getr regs 1)).
Lemma fm_frame_kept : forall sp0 m m' regs, fm_frame sp0 m regs ->
  (forall a, sp0 - 48 <= a < sp0 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> fm_frame sp0 m' regs.
Proof.
intros sp0 m m' regs (F1 & F2 & F3 & F4 & F5 & F6) Hk.
unfold fm_frame. repeat split;
  (eapply fm_vm_fr; [|eassumption]); intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia.
Qed.

Ltac pks := cbv [asrc_env_addr as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary as_ofl_head pcap_KS
  PCAP_THREADED PCAP_NEED_LOCKS PCAP_OFL_LOCK PCAP_MODE PCAP_RWA PCAP_CANARY].

(* ---------------------------------------------------------------------------------------------- *)
(* 5. The walk, over pcap's ASan image tfibsegs = Asan.M.loaded_segments.                          *)
(* ---------------------------------------------------------------------------------------------- *)
Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.
Local Abbreviation AJ := (@ajournal rc SK tfibsegs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation STK := RFMEMOPEN_STK.

(* NAMED SECTION HYPOTHESES. *)
(* The read stream's image laws (a Theorem Labs lane's PSourceMeta.v), discharged once with the core's B. *)
Hypothesis ASIL : asource_img_laws SK tfibsegs B pcap_KS.
(* The core's symbol record for pcap's ASan image (A/AF0m.v, gated PASS A+B at c061542723f / 731386609e0). *)
Hypothesis TL : PcapSyms B.
(* The ASan memset interceptor at its trampoline 0x5150c (cgif's AINTR, A/AE25.v:74). The core's
   A/AE32.v memset_icpt_realizes states exactly this (premises reordered), but at a working branch e8bb946b7e4 it
   does not build: its import A/AE79.v fails (`pcap_img_end` not found). *)
Hypothesis AINTR : aintrin_realizes tfibsegs B OSet FM_MEMSET.

(* 5.1 The strchr cells come from AR and the stdio environment (cgif A/AE6i.v tfib_ff_cells_ok's method). *)
Lemma fm_cells : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> asrc_stdio_env tfibsegs pcap_KS (rd W mem) ->
  cells_hold (rd W mem) st_cells.
Proof.
intros ly S W mem md HAR HENV.
pose proof (proj1 HAR) as HM.
pose proof HENV as (_ & _ & _ & Emode & _).
assert (C8 : forall a v, const_chk ly a 8%N v = true -> val_mem tfibsegs (rd W mem) a 8 v).
{ intros a v Hc. exact (tfib_const_lookup B TL ly S (w_H W) mem a 8%nat v HM (const_chk_sound _ _ _ _ Hc)). }
assert (C1 : forall a v, const_chk ly a 1%N v = true -> 0 <= v < 256 -> mbyte tfibsegs (rd W mem) a = Some (Z_to_bv 8 v)).
{ intros a v Hc Hv. pose proof (tfib_const_lookup B TL ly S (w_H W) mem a 1%nat v HM (const_chk_sound _ _ _ _ Hc) 0%nat ltac:(lia)) as X.
  rewrite Z.add_0_r in X. rewrite X. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity. }
assert (ZS : forall lo len x, In (lo, len) Tfib_zero_shadow -> SHADOW_OFF + lo / 8 <= x < SHADOW_OFF + lo / 8 + len / 8 ->
  mbyte tfibsegs (rd W mem) x = Some (Z_to_bv 8 0)).
{ intros lo len x Hin Hx. apply aview_byte.
  pose proof (YG0s.AR_zshadow_law_ok tfibsegs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TL); exact Hin)) as Z0.
  cbn [fst snd] in Z0. specialize (Z0 (x - (SHADOW_OFF + lo / 8)) ltac:(lia)). unfold YG0v.shadow_of_addr in Z0.
  replace (SHADOW_OFF + lo / 8 + (x - (SHADOW_OFF + lo / 8))) with x in Z0 by lia. exact Z0. }
assert (ZS1 : forall x, 0x7fffc000 <= x < 0x7fffc008 -> mbyte tfibsegs (rd W mem) x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply (ZS 0x10000 ((symaddr (Symbols.Asan.Sec.s_rodata + 68136)%Z) - 0x10000)); [unfold Tfib_zero_shadow; left; reflexivity | unfold SHADOW_OFF; lia]. }
assert (ZS2 : forall x, 0x7fffc1ac <= x < 0x7fffc1b0 -> mbyte tfibsegs (rd W mem) x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply (ZS (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z) ((symaddr Symbols.Asan.Sec.s_asan_globals) - (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z))); [unfold Tfib_zero_shadow; right; right; left; reflexivity | unfold SHADOW_OFF; lia]. }
assert (RB : forall j, (j < 3)%nat -> mbyte tfibsegs (rd W mem) (FM_MODE + Z.of_nat j) = Some (Z_to_bv 8 (nth j [114; 98; 0] 0))).
{ intros j Hj. exact (fm_garr8_byte _ (as_mode pcap_KS) _ j Emode ltac:(cbn; lia)). }
unfold cells_hold, st_cells, A_RB.
repeat (apply Forall_cons; [cbn [fst snd]; split; [unfold FM_MODE; lia|]; split; [unfold FM_MODE; lia|];
  apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split; [|split; [cbn; lia | cbn; lia]] |]); [| | | | apply Forall_nil].
- rewrite Z.add_0_r. apply C8. vm_compute. reflexivity.
- intros k Hk. cbn [N.to_nat Pos.to_nat] in Hk.
  replace (YO0f.le_byte 0 (N.to_nat 8) k) with 0
    by (unfold YO0f.le_byte; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity).
  apply ZS1. lia.
- intros k Hk. cbn [N.to_nat Pos.to_nat] in Hk.
  do 8 (destruct k as [|k];
    [ match goal with |- mbyte _ _ ?a = Some (Z_to_bv 8 ?v) =>
        let a' := eval vm_compute in a in let v' := eval vm_compute in v in change a with a'; change v with v' end;
      first [ apply ZS2; lia | apply C1; [vm_compute; reflexivity | lia] ] |]).
  lia.
- intros k Hk. cbn [N.to_nat Pos.to_nat] in Hk.
  do 8 (destruct k as [|k];
    [ match goal with |- mbyte _ _ ?a = Some (Z_to_bv 8 ?v) =>
        let a' := eval vm_compute in a in let v' := eval vm_compute in v in change a with a'; change v with v' end;
      first [ apply C1; [vm_compute; reflexivity | lia]
            | match goal with |- mbyte _ _ ?a = Some (Z_to_bv 8 ?v) =>
                let j := eval vm_compute in (Z.to_nat (a - FM_MODE)) in
                pose proof (RB j ltac:(lia)) as X; cbn [nth Z.of_nat Pos.of_succ_nat] in X;
                unfold FM_MODE in X; cbn in X; exact X end ] |]).
  lia.
Qed.

(* 5.2 The one "rwa" byte strchr loads (a Theorem Labs lane's rwa_img) is pinned by the stdio environment. *)
Lemma fm_rwa_img : forall (W : world tfibsegs) mem, asrc_stdio_env tfibsegs pcap_KS (rd W mem) -> rwa_img (rd W mem).
Proof.
intros W mem HENV a Ha. pose proof HENV as (_ & _ & _ & _ & Erwa & _).
unfold A_RWA, RWA_LD in Ha. assert (a = (symaddr (Symbols.Asan.Sec.s_rodata + 0xfd46)%Z)) as -> by lia.
pose proof (fm_garr8_byte _ (as_rwa pcap_KS) _ 0 Erwa ltac:(cbn; lia)) as X.
change (as_rwa pcap_KS + Z.of_nat 0) with (symaddr (Symbols.Asan.Sec.s_rodata + 0xfd46)%Z) in X. change (nth 0 (src_modeset_Z ++ [0]) 0) with 114 in X.
exists (Z_to_bv 8 114). split; [vm_compute; reflexivity | exact X].
Qed.

(* 5.3 One strchr call, composed with the journal (both calls happen before malloc: lyc Sc = ly S). *)
Lemma fm_strchr_step : forall s c res (W W0 : world tfibsegs) ly S mem0 md0 regs mem md sp0
    (Q : world tfibsegs -> config -> Prop),
  In (s, c, res) [(FM_RWA, 114, FM_RWA); (FM_MODE, 43, 0)] ->
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 ->
  spZ regs = sp0 - 48 -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  cells_hold (rd W mem) st_cells -> rwa_img (rd W mem) -> mconsts_view W mem ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 10 = w64 res -> getr regs1 1 = getr regs 1 -> getr regs1 2 = getr regs 2 ->
     (forall r, In r KEPTS -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 - SC_WIN <= a < sp0 - 48) ->
        aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W (cfg_at tfibsegs (raZ regs) regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_STRCHR regs mem md) Q.
Proof.
intros s c res W W0 ly S mem0 md0 regs mem md sp0 Q Hin HJ Hsp Hra G10 G11 HCL HRW HMC K.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
eapply SRr_bind.
{ apply (tfib_strchr_lit B LAWS TL s c res ltac:(unfold INST, A_RWA, A_RB; exact Hin) ly S W regs mem md HAR Hra);
    try assumption.
  - rewrite Hsp. lia.
  - unfold SC_WIN. rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - intros a Ha. apply Hpres. rewrite Hsp in Ha. unfold SC_WIN in Ha. lia. }
cbv beta. intros W' c' _ (-> & regs1 & mem1 & md1 & -> & SBM & HAR1 & H10 & H1 & H2 & HK & AV & PRS & PM).
rewrite Hsp in AV, PRS.
apply K; [| exact SBM | exact H10 | exact H1 | exact H2 | exact HK | exact AV].
eapply (ajournal_after_write tfibsegs B LAWS fm_segs_low STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 mem1 md1
  (fun a => sp0 - 48 - SC_WIN <= a < sp0 - 48) S [] HJ).
- intros a Ha Hna. exact (AV a Ha Hna).
- exact PM.
- exact SBM.
- intros a Ha. left. left. rewrite FS. unfold SC_WIN in Ha. lia.
- exact HAR1.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

(* 5.4 The journal across a write confined to musl's open-file-list head (8 bytes at 0x5f4f88): a Theorem Labs lane's
   wf_frameW / wf_journal_write (lib/A/Stdio/WFclose.v) for the head alone. awr_byte (YCbq.v:457) has no
   case for the head; the journal keeps it free because the footprint holds the sink token (fp_spares). *)
Lemma fm_head_journal : forall sp0 ly S (W0 W : world tfibsegs) mem0 md0 lyc Sc mem mdc k mem1 md1,
  AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem mdc k ->
  (forall x : word, ~ (FM_HEAD <= bv_unsigned x < FM_HEAD + 8) -> mem1 x = mem x) ->
  (forall a, FM_HEAD <= a < FM_HEAD + 8 -> aview tfibsegs (w_H W) mem1 a <> None) ->
  same_but_materialized mdc md1 ->
  AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem1 md1 k.
Proof.
intros sp0 ly S W0 W mem0 md0 lyc Sc mem mdc k mem1 md1 HJ MEQ HV MF.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres
                  & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
assert (HHD : @AOFL_HEAD SK = FM_HEAD) by (rewrite <- (asil_head _ _ _ _ ASIL); reflexivity).
assert (HIMG : forall a, FM_HEAD <= a < FM_HEAD + 8 ->
  in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (asil_env _ _ _ _ ASIL a). pks. unfold FM_HEAD in Ha. lia. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (FM_HEAD <= a < FM_HEAD + 8) ->
  aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. unfold mrestrict. destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  apply MEQ. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (HAR1 : AR tfibsegs B lyc Sc W mem1 md1).
{ pose proof (same_but_materialized_frame mdc md1 MF)
    as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Feu).
  apply (al_frame _ _ LAWS lyc Sc W mem mdc mem1 md1 HAR).
  - intros a Ha Hown. destruct (Z_lt_le_dec a FM_HEAD) as [L|L]; [apply AV; [exact Ha | lia]|].
    destruct (Z_lt_le_dec a (FM_HEAD + 8)) as [L2|L2]; [|apply AV; [exact Ha | lia]].
    exfalso. destruct (HIMG a (conj L L2)) as (Hi & Hns & _). apply Hns.
    exact (proj1 (al_owned_image _ _ LAWS lyc Sc W mem mdc a HAR Hi) Hown).
  - intros a Hv. rewrite (fm_aview_mod (w_H W) mem1 a). rewrite (fm_aview_mod (w_H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) FM_HEAD) as [L|L]; [rewrite AV by (lia || (intros X; lia)); exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (FM_HEAD + 8)) as [L2|L2]; [exact (HV _ (conj L L2))|].
    rewrite AV by (lia || (intros X; lia)). exact Hv.
  - exact Fmaps.
  - exact Flazy.
  - exact Feu.
  - intros a Hband Hh. apply MEQ. unfold w64.
    assert (Hra : 0 <= a < 2 ^ 64)
      by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband; lia).
    rewrite unsigned_lit_small by exact Hra.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. unfold FM_HEAD. lia. }
split; [exact HAR1|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, MF]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply AV; [lia | unfold FM_HEAD; lia]. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (al_blocks _ _ LAWS lyc Sc W mem mdc p n HAR H2) as (_ & Hp0 & Hpc & _).
  apply AV; [lia|]. intros Ho. exact (blk_img tfibsegs B LAWS lyc Sc W mem mdc p n (p + i) HAR H2 ltac:(lia) (proj1 (HIMG _ Ho))). }
split.
{ intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (fm_segs_low a Hi) as Ra.
  apply AV; [unfold kLowMemEnd in Ra; lia|]. intros Ho. apply (Hsp (YI16.sink_open_token FPT ltac:(left; reflexivity))).
  rewrite HHD. exact Ho. }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hin).
  assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W mem mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfapp).
  rewrite Efr in Hf0, Hfc. pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. destruct Hr as [Hr | Hr].
  - apply AV; [lia|]. intros Ho.
    apply (frm_img tfibsegs B LAWS lyc Sc W mem mdc cid pos a HAR HinC ltac:(rewrite Efr; lia) (proj1 (HIMG _ Ho))).
  - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(unfold kHighMemEnd; lia)) as [B1 B2].
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; lia)) as [U1 U2].
    apply AV; unfold kLowMemEnd, kHighShadowEnd, FM_HEAD in *; lia. }
split; [exact Hgone|].
split.
{ intros a Ha. destruct (Hpres a Ha) as [Hh [bt Hb]]. split; [exact Hh|]. exists bt. rewrite MEQ; [exact Hb|].
  rewrite unsigned_lit_small by lia. unfold FM_HEAD. lia. }
split; [exact Hstatic|].
split; [| exact HQT].
{ intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
  pose proof (YG0p.AR_extra_law_ok tfibsegs B lyc Sc W mem mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
  apply AV.
  - unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. lia.
  - intros Ho. exact (Xi (proj1 (HIMG _ Ho))). }
Qed.

(* 5.5 The stdio environment survives any journal: its cells are image bytes outside the head. *)
Lemma fm_env_kept : forall STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  AJ STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  asrc_stdio_env tfibsegs pcap_KS (rd W mem) -> asrc_stdio_env tfibsegs pcap_KS (rd W' mem').
Proof.
intros STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ (H1 & H2 & H3 & H4 & H5 & (cv & Hcv & H6)).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (FR : forall a, (a = as_threaded pcap_KS \/ a = as_need_locks pcap_KS \/
    (as_ofl_lock pcap_KS <= a < as_ofl_lock pcap_KS + 4) \/ (as_mode pcap_KS <= a < as_mode pcap_KS + 3) \/
    (as_rwa pcap_KS <= a < as_rwa pcap_KS + 4) \/ (as_canary pcap_KS <= a < as_canary pcap_KS + 8)) ->
  mbyte tfibsegs (rd W' mem') a = mbyte tfibsegs (rd W mem) a).
{ intros a Ha. apply mbyte_of_aview.
  destruct (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr; lia)) as (Hi & Hns & He).
  apply (F3 a Hi Hns He). apply fp_spares_off. exact (asil_env_static _ _ _ _ ASIL a Ha). }
split; [eapply fm_vm_fr; [|exact H1]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply fm_vm_fr; [|exact H2]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply fm_vm_fr; [|exact H3]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply garr8_frame; [exact H4|]; intros x Hx; apply FR; unfold src_mode_Z in Hx; cbn [length app] in Hx; simpl Z.of_nat in Hx; lia|].
split; [eapply garr8_frame; [exact H5|]; intros x Hx; apply FR; unfold src_modeset_Z in Hx; cbn [length app] in Hx; simpl Z.of_nat in Hx; lia|].
exists cv. split; [exact Hcv|]. eapply fm_vm_fr; [|exact H6]. intros x Hx. apply FR. simpl Z.of_nat in Hx. lia.
Qed.

Ltac fm_lit E ss HS v := erewrite (fm_reg_of E ss _ _ _ (SLit v)); [reflexivity | exact HS | vm_compute; reflexivity].
Lemma fm_keep_of : forall E ss (H : word -> bool) ms regs xs, st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs xs ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) [3; 4; 21; 22; 23; 24; 25; 26; 27] = true ->
  fm_keep regs (ms_regs ms).
Proof.
intros E ss H ms regs xs HS HE Hb r Hr. apply (fm_reg_kept E ss H ms regs xs r HS HE).
- cbn [In] in Hr. lia.
- rewrite forallb_forall in Hb. apply sv_eqb_eq. exact (Hb r Hr).
Qed.

(* 5.6 Phase A: the entry, up to the first strchr call. *)
Lemma fm_A : forall (W W0 : world tfibsegs) ly S mem0 md0 regs mem md (Q : world tfibsegs -> config -> Prop),
  AJ STK (spZ regs) FPT ly S W0 mem0 md0 [] ly S W mem md 0 ->
  getr regs 12 = w64 FM_MODE ->
  (forall regs1 mem1 md1,
     AJ STK (spZ regs) FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 FM_RA1 -> getr regs1 2 = w64 (spZ regs - 48) ->
     getr regs1 10 = w64 FM_MODE -> getr regs1 11 = w64 43 ->
     getr regs1 8 = getr regs 8 -> getr regs1 9 = getr regs 10 -> getr regs1 18 = getr regs 11 ->
     getr regs1 19 = w64 FM_MODE -> getr regs1 20 = getr regs 20 ->
     fm_keep regs regs1 ->
     fm_frame (spZ regs) (rd W mem1) regs ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
        mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     SRr tfibsegs W (cfg_at tfibsegs FM_STRCHR regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs PFMEMOPEN regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 regs mem md Q HJ G12 K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
set (sp0 := spZ regs) in *.
remember (Ereg regs []) as E eqn:HE.
assert (E2u : bv_unsigned (ew E 2) = sp0) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 PFMEMOPEN) with (Z_to_bv 64 (ss_pc ssA)).
assert (HS : st_ok tfibsegs E ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssA)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X | rewrite G12; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold stkA.
    apply (region_ok_stack tfibsegs E _ 2 sp0 (-48)); [exact E2u | lia | lia |].
    intros a Ha. apply apresent_writable. apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2u.
    change (2 ^ 4) with 16. repeat split; lia. }
eapply (SRr_run_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL E ssA eA _ _ STK sp0 FPT ly S W0 mem0 md0
  [] ly S md 0 Q HS r_A I HJ).
{ unfold ssA. cbn [ss_mem].
  eapply (awr_ok_cons_stack E stkA [] STK sp0 FPT (ablocks B ly S) (ablocks B ly S) ly [] 2);
    [reflexivity | exact E2u | cbn [YP09.r_wlo stkA]; rewrite FS; lia | cbn [YP09.r_whi stkA]; lia | apply awr_ok_nil]. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eA ms1 HS1 eq_refl).
assert (FV : forall off (r : nat), chunk_at eA 0 off 8 (SOff r 0) = true -> (r < 32)%nat ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))).
{ intros off r Hc Hr. pose proof (fm_chunk_val E eA (w_H W) ms1 0 off 8 (SOff r 0) 2 HS1 Hc eq_refl ltac:(lia)) as V.
  rewrite E2u, (fm_soff0 E r (getr regs (Z_to_bv 5 (Z.of_nat r)))) in V; [exact V|].
  rewrite HE. apply ew_Ereg_lt. exact Hr. }
refine (K (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) HJ1 (with_vm_backing_same md mat1)
  _ _ _ _ _ _ _ _ _ _ _ _).
- fm_lit E eA HS1 FM_RA1.
- rewrite (fm_reg_of E eA _ ms1 2%bv (SOff 2 (-48)) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2u.
  unfold w64. f_equal; lia.
- fm_lit E eA HS1 FM_MODE.
- fm_lit E eA HS1 43.
- exact (fm_reg_kept E eA _ ms1 regs [] 8 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- rewrite (fm_reg_of E eA _ ms1 9%bv (SOff 10 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite HE, (ew_Ereg_nat regs [] 10 10%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (fm_reg_of E eA _ ms1 18%bv (SOff 11 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite HE, (ew_Ereg_nat regs [] 11 11%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned.
- fm_lit E eA HS1 FM_MODE.
- exact (fm_reg_kept E eA _ ms1 regs [] 20 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_keep_of E eA _ _ regs (@nil word) HS1 HE ltac:(vm_compute; reflexivity)).
- unfold fm_frame.
  split; [replace (sp0 - 48) with (sp0 + -48) by lia; exact (FV (-48) 20%nat ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [replace (sp0 - 40) with (sp0 + -40) by lia; exact (FV (-40) 19%nat ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [replace (sp0 - 32) with (sp0 + -32) by lia; exact (FV (-32) 18%nat ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [replace (sp0 - 24) with (sp0 + -24) by lia; exact (FV (-24) 9%nat ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [replace (sp0 - 16) with (sp0 + -16) by lia; exact (FV (-16) 8%nat ltac:(vm_compute; reflexivity) ltac:(lia))|].
  replace (sp0 - 8) with (sp0 + -8) by lia; exact (FV (-8) 1%nat ltac:(vm_compute; reflexivity) ltac:(lia)).
- intros a Ha Hn. apply (fm_mb_frame E (ss_mem ssA) _ _ a HFr1 Ha). unfold ssA. cbn [ss_mem]. apply fm_nwr_all.
  apply Forall_cons; [|apply Forall_nil]. unfold stkA. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite E2u. lia.
Qed.

(* 5.7 Phase B: from the first strchr's return to the second strchr call. *)
Lemma fm_B : forall (W W0 : world tfibsegs) ly S mem0 md0 sp0 regs mem md (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 ->
  getr regs 10 = w64 0 -> getr regs 19 = w64 FM_MODE ->
  val_mem tfibsegs (rd W mem) FM_MODE 1 114 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 FM_RA2 -> getr regs1 10 = w64 FM_RWA -> getr regs1 11 = w64 114 ->
     getr regs1 19 = w64 FM_MODE -> getr regs1 20 = w64 0 ->
     getr regs1 2 = getr regs 2 -> getr regs1 8 = getr regs 8 -> getr regs1 9 = getr regs 9 ->
     getr regs1 18 = getr regs 18 -> fm_keep regs regs1 ->
     (forall a, 0 <= a < 2 ^ 64 -> mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     SRr tfibsegs W (cfg_at tfibsegs FM_STRCHR regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_RA1 regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 sp0 regs mem md Q HJ G10 G19 VM K.
remember (Ereg regs []) as E eqn:HE.
unfold cfg_at. change (w64 FM_RA1) with (Z_to_bv 64 (ss_pc ssB)).
assert (HS : st_ok tfibsegs E ssB (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssB)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssB. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X | rewrite G10; reflexivity]
                       | intros X; discriminate X | rewrite G19; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold modeR, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold FM_MODE; lia|]. split; [unfold FM_MODE; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. unfold ck.
    apply (chunk_ok_val tfibsegs E _ 0 FM_MODE 1%N (SLit 114) 114); [reflexivity | cbn; lia | cbn; lia | exact VM].
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
eapply (SRr_run_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL E ssB eB _ _ STK sp0 FPT ly S W0 mem0 md0
  [] ly S md 0 Q HS r_B I HJ).
{ unfold ssB. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eB ms1 HS1 eq_refl).
refine (K (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) HJ1 (with_vm_backing_same md mat1)
  _ _ _ _ _ _ _ _ _ _ _).
- fm_lit E eB HS1 FM_RA2.
- fm_lit E eB HS1 FM_RWA.
- fm_lit E eB HS1 114.
- fm_lit E eB HS1 FM_MODE.
- fm_lit E eB HS1 0.
- exact (fm_reg_kept E eB _ ms1 regs [] 2 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eB _ ms1 regs [] 8 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eB _ ms1 regs [] 9 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eB _ ms1 regs [] 18 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_keep_of E eB _ _ regs (@nil word) HS1 HE ltac:(vm_compute; reflexivity)).
- intros a Ha. apply (fm_mb_frame E (ss_mem ssB) _ _ a HFr1 Ha). unfold ssB. cbn [ss_mem]. apply fm_nwr_all.
  apply Forall_cons; [|apply Forall_nil]. unfold modeR. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. lia.
Qed.

(* 5.8 Phase C: from the second strchr's return to the malloc call (the EINVAL / ENOMEM arms are not taken). *)
Lemma fm_C : forall (W W0 : world tfibsegs) ly S mem0 md0 sp0 regs mem md (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 ->
  getr regs 10 = w64 FM_RWA -> 4096 <= bv_unsigned (getr regs 9) <= 2 ^ 47 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 FM_MALLOC_RA -> getr regs1 10 = w64 SRC_FILE_BLOCK ->
     getr regs1 2 = getr regs 2 -> getr regs1 8 = getr regs 8 -> getr regs1 9 = getr regs 9 ->
     getr regs1 18 = getr regs 18 -> getr regs1 19 = getr regs 19 -> getr regs1 20 = getr regs 20 ->
     fm_keep regs regs1 ->
     (forall a, 0 <= a < 2 ^ 64 -> mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     SRr tfibsegs W (cfg_at tfibsegs FM_MALLOC regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_RA2 regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 sp0 regs mem md Q HJ G10 Hb9 K.
remember (Ereg regs []) as E eqn:HE.
assert (E9u : bv_unsigned (ew E 9) = bv_unsigned (getr regs 9)) by (rewrite HE, (ew_Ereg_nat regs _ 9 9%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 FM_RA2) with (Z_to_bv 64 (ss_pc ssC)).
assert (HS : st_ok tfibsegs E ssC (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssC)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X | rewrite G10; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9u.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
eapply (SRr_run_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL E ssC eC _ _ STK sp0 FPT ly S W0 mem0 md0
  [] ly S md 0 Q HS r_C I HJ).
{ unfold ssC. cbn [ss_mem]. apply awr_ok_nil. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eC ms1 HS1 eq_refl).
refine (K (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) HJ1 (with_vm_backing_same md mat1)
  _ _ _ _ _ _ _ _ _ _).
- fm_lit E eC HS1 FM_MALLOC_RA.
- fm_lit E eC HS1 SRC_FILE_BLOCK.
- exact (fm_reg_kept E eC _ ms1 regs [] 2 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eC _ ms1 regs [] 8 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eC _ ms1 regs [] 9 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eC _ ms1 regs [] 18 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eC _ ms1 regs [] 19 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eC _ ms1 regs [] 20 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_keep_of E eC _ _ regs (@nil word) HS1 HE ltac:(vm_compute; reflexivity)).
- intros a Ha. apply (fm_mb_frame E (ss_mem ssC) _ _ a HFr1 Ha). unfold ssC. cbn [ss_mem]. apply fm_nwr_all.
  apply Forall_nil.
Qed.

(* 5.9 Phase D: from malloc's return (res >= 4096, so `bnez a0` at 0x8e90c is taken) to the memset call. *)
Lemma fm_D : forall (W W0 : world tfibsegs) ly S mem0 md0 lyc Sc sp0 regs mem md k (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem md k ->
  4096 <= bv_unsigned (getr regs 10) <= 2 ^ 47 -> bv_unsigned (getr regs 10) mod 16 = 0 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem1 md1 k ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 FM_RA4 -> getr regs1 10 = getr regs 10 -> getr regs1 8 = getr regs 10 ->
     getr regs1 11 = w64 0 -> getr regs1 12 = w64 272 ->
     getr regs1 2 = getr regs 2 -> getr regs1 9 = getr regs 9 -> getr regs1 18 = getr regs 18 ->
     getr regs1 19 = getr regs 19 -> getr regs1 20 = getr regs 20 ->
     fm_keep regs regs1 ->
     (forall a, 0 <= a < 2 ^ 64 -> mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     SRr tfibsegs W (cfg_at tfibsegs FM_MEMSET regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_MALLOC_RA regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 lyc Sc sp0 regs mem md k Q HJ Hb10 Hal10 K.
remember (Ereg regs []) as E eqn:HE.
assert (E10u : bv_unsigned (ew E 10) = bv_unsigned (getr regs 10)) by (rewrite HE, (ew_Ereg_nat regs _ 10 10%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 FM_MALLOC_RA) with (Z_to_bv 64 (ss_pc ssD)).
assert (HS : st_ok tfibsegs E ssD (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssD)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssD. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10u.
    change (2 ^ 4) with 16. repeat split; lia. }
eapply (SRr_run_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL E ssD eD _ _ STK sp0 FPT ly S W0 mem0 md0
  [] lyc Sc md k Q HS r_D I HJ).
{ unfold ssD. cbn [ss_mem]. apply awr_ok_nil. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eD ms1 HS1 eq_refl).
refine (K (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) HJ1 (with_vm_backing_same md mat1)
  _ _ _ _ _ _ _ _ _ _ _ _).
- fm_lit E eD HS1 FM_RA4.
- exact (fm_reg_kept E eD _ ms1 regs [] 10 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- rewrite (fm_reg_of E eD _ ms1 8%bv (SOff 10 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite HE, (ew_Ereg_nat regs [] 10 10%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned.
- fm_lit E eD HS1 0.
- fm_lit E eD HS1 272.
- exact (fm_reg_kept E eD _ ms1 regs [] 2 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eD _ ms1 regs [] 9 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eD _ ms1 regs [] 18 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eD _ ms1 regs [] 19 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_reg_kept E eD _ ms1 regs [] 20 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
- exact (fm_keep_of E eD _ _ regs (@nil word) HS1 HE ltac:(vm_compute; reflexivity)).
- intros a Ha. apply (fm_mb_frame E (ss_mem ssD) _ _ a HFr1 Ha). unfold ssD. cbn [ss_mem]. apply fm_nwr_all.
  apply Forall_nil.
Qed.

(* 5.10 The FILE fields fmemopen sets, as asource_unbuffered reads them (PSource.v section 3-6). *)
Definition fm_file (m : word -> option byte) (f : Z) (bw nw : word) : Prop :=
  val_mem tfibsegs m (f + 0) 4 8 /\ val_mem tfibsegs m (f + 8) 8 0 /\ val_mem tfibsegs m (f + 16) 8 0 /\
  val_mem tfibsegs m (f + 24) 8 PCAP_MCLOSE /\
  val_mem tfibsegs m (f + 32) 8 0 /\ val_mem tfibsegs m (f + 40) 8 0 /\ val_mem tfibsegs m (f + 48) 8 0 /\
  val_mem tfibsegs m (f + 56) 8 0 /\
  val_mem tfibsegs m (f + 64) 8 PCAP_MREAD /\ val_mem tfibsegs m (f + 72) 8 PCAP_MWRITE /\
  val_mem tfibsegs m (f + 80) 8 PCAP_MSEEK /\ val_mem tfibsegs m (f + 88) 8 (f + 280) /\
  val_mem tfibsegs m (f + 96) 8 1024 /\ val_mem tfibsegs m (f + 104) 8 0 /\ val_mem tfibsegs m (f + 112) 8 0 /\
  val_mem tfibsegs m (f + 120) 4 U32M1 /\ val_mem tfibsegs m (f + 136) 4 0 /\
  val_mem tfibsegs m (f + 140) 4 U32M1 /\ val_mem tfibsegs m (f + 144) 4 U32M1 /\
  val_mem tfibsegs m (f + 152) 8 (f + 232) /\ val_mem tfibsegs m (f + 168) 8 0 /\ val_mem tfibsegs m (f + 232) 8 0 /\
  val_mem tfibsegs m (f + 240) 8 (bv_unsigned nw) /\ val_mem tfibsegs m (f + 248) 8 (bv_unsigned nw) /\
  val_mem tfibsegs m (f + 256) 8 (bv_unsigned bw) /\ val_mem tfibsegs m (f + 264) 4 114.

Lemma fm_file_kept : forall m m' f bw nw, fm_file m f bw nw ->
  (forall a, f <= a < f + 272 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> fm_file m' f bw nw.
Proof.
intros m m' f bw nw H Hk. unfold fm_file in *.
repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  end.
repeat split; (eapply fm_vm_fr; [|eassumption]); intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia.
Qed.

Lemma fm_chunk_word : forall E m base off (x : word) (n : nat), ew E n = x ->
  val_mem tfibsegs m (base + off) 8 (bv_unsigned x) -> YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m base off x n Hx Hv. apply (chunk_ok_val tfibsegs E m base off 8%N (SOff n 0) (bv_unsigned x)).
- cbn [sv_denot]. rewrite Hx, Z.add_0_r. reflexivity.
- pose proof (u64_range x). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
- exact Hv.
Qed.

Lemma fm_off_val : forall E n z b, bv_unsigned (ew E n) = b -> 0 <= b + z < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n z)) mod 2 ^ (8 * Z.of_N 8) = b + z.
Proof.
intros E n z b H Hr. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hr.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_small. exact Hr.
Qed.

Lemma fm_chunk_val0 : forall E ss (H : word -> bool) ms i off n v,
  st_ok tfibsegs E ss (restrict H ms) -> chunk_at ss i off n v = true -> rbase_at ss i = None -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (0 + off) (N.to_nat n) (bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E ss H ms i off n v HS Hc Hb Hn.
unfold chunk_at, rbase_at in *. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
apply existsb_exists in Hc as ([o cv] & Hin & Hck). cbn [YP09.c_off YP09.c_val] in Hck.
apply andb_prop in Hck as [Ho Hcv]. apply Z.eqb_eq in Ho. subst o.
destruct cv as [n' e|l0|l0|d0 s0 l0]; try discriminate. apply andb_prop in Hcv as [Hn' He].
apply N.eqb_eq in Hn'. apply sv_eqb_eq in He. subst n' e.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
exact (YC4b.val_of_chunk_any tfibsegs E _ _ off n v Hck Hn).
Qed.

(* 5.11 Phase E: from memset's return through the FILE set-up, the epilogue, the tail jump into __ofl_add,
   __ofl_lock / __lock (need_locks = 0) and f->next = old head (0), up to the head store 0x8f23c. *)
Lemma fm_E : forall (W W0 : world tfibsegs) ly S mem0 md0 ly2 S2 sp0 regs regs0 mem md res
    (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly2 S2 W mem md 1 ->
  In (res, SRC_FILE_BLOCK) (ablocks B ly2 S2) -> ~ In (res, SRC_FILE_BLOCK) (ablocks B ly S) ->
  spZ regs = sp0 - 48 -> getr regs 8 = w64 res ->
  4096 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> getr regs 19 = w64 FM_MODE -> getr regs 20 = w64 0 ->
  fm_frame sp0 (rd W mem) regs0 ->
  (forall i, 0 <= i < 272 -> mbyte tfibsegs (rd W mem) (res + i) = Some (Z_to_bv 8 0)) ->
  val_mem tfibsegs (rd W mem) FM_MODE 1 114 -> val_mem tfibsegs (rd W mem) FM_THR 1 0 ->
  val_mem tfibsegs (rd W mem) FM_NL 1 0 -> val_mem tfibsegs (rd W mem) FM_HEAD 8 0 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly2 S2 W mem1 md1 1 ->
     same_but_materialized md md1 ->
     getr regs1 10 = w64 FM_HEAD -> getr regs1 2 = w64 (sp0 - 16) -> getr regs1 8 = w64 res ->
     getr regs1 9 = getr regs0 9 -> getr regs1 18 = getr regs0 18 -> getr regs1 19 = getr regs0 19 ->
     getr regs1 20 = getr regs0 20 -> fm_keep regs regs1 ->
     val_mem tfibsegs (rd W mem1) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
     val_mem tfibsegs (rd W mem1) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
     fm_file (rd W mem1) res (getr regs 9) (getr regs 18) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> ~ (res <= a < res + 272) ->
        mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     SRr tfibsegs W (cfg_at tfibsegs FM_HEADST regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_RA4 regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 ly2 S2 sp0 regs regs0 mem md res Q HJ Hblk2 Hnew Hsp G8 Hb9 G19 G20 HFR HZ
  VMODE VTHR VNL VHEAD K.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
destruct (al_blocks _ _ LAWS ly2 S2 W mem md res SRC_FILE_BLOCK HAR Hblk2) as (Hf16 & Hf4 & Hfceil & Hfapp & Hfb & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil, Hfb.
assert (IMGX : forall a, (FM_MODE <= a < FM_MODE + 3) \/ a = FM_THR \/ a = FM_NL \/ (FM_HEAD <= a < FM_HEAD + 8) ->
  in_img tfibsegs a).
{ intros a Ha. apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(pks; unfold FM_MODE, FM_THR, FM_NL, FM_HEAD in Ha; lia))). }
assert (DJ : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> in_img tfibsegs a) -> res + 1304 <= lo \/ hi <= res).
{ intros lo hi Hlh Hi. destruct (Z_le_gt_dec lo res) as [L|L].
  - destruct (Z_lt_ge_dec res hi) as [L2|L2]; [|right; lia]. exfalso.
    apply (blk_img tfibsegs B LAWS ly2 S2 W mem md res SRC_FILE_BLOCK res HAR Hblk2);
      [change (req_size SRC_FILE_BLOCK) with 1304; lia | apply Hi; lia].
  - destruct (Z_lt_ge_dec lo (res + 1304)) as [L2|L2]; [|left; lia]. exfalso.
    apply (blk_img tfibsegs B LAWS ly2 S2 W mem md res SRC_FILE_BLOCK lo HAR Hblk2);
      [change (req_size SRC_FILE_BLOCK) with 1304; lia | apply Hi; lia]. }
pose proof (DJ FM_MODE (FM_MODE + 3) ltac:(lia) (fun a Ha => IMGX a ltac:(lia))) as DJm.
pose proof (DJ FM_THR (FM_THR + 1) ltac:(lia) (fun a Ha => IMGX a ltac:(lia))) as DJt.
pose proof (DJ FM_NL (FM_NL + 1) ltac:(lia) (fun a Ha => IMGX a ltac:(lia))) as DJn.
pose proof (DJ FM_HEAD (FM_HEAD + 8) ltac:(lia) (fun a Ha => IMGX a ltac:(lia))) as DJh.
remember (Ereg regs [getr regs0 20; getr regs0 19; getr regs0 18; getr regs0 9; getr regs0 8; getr regs0 1]) as E eqn:HE.
assert (E2u : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E8u : bv_unsigned (ew E 8) = res).
{ rewrite HE, (ew_Ereg_nat regs _ 8 8%bv eq_refl), G8. apply unsigned_lit_small. lia. }
assert (E9 : ew E 9 = getr regs 9) by (rewrite HE; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite HE; exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E32 : ew E 32 = getr regs0 20) by (rewrite HE; reflexivity).
assert (E33 : ew E 33 = getr regs0 19) by (rewrite HE; reflexivity).
assert (E34 : ew E 34 = getr regs0 18) by (rewrite HE; reflexivity).
assert (E35 : ew E 35 = getr regs0 9) by (rewrite HE; reflexivity).
assert (E36 : ew E 36 = getr regs0 8) by (rewrite HE; reflexivity).
assert (E37 : ew E 37 = getr regs0 1) by (rewrite HE; reflexivity).
pose proof HFR as (F1 & F2 & F3 & F4 & F5 & F6).
unfold cfg_at. change (w64 FM_RA4) with (Z_to_bv 64 (ss_pc ssE)).
assert (HS : st_ok tfibsegs E ssE (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssE)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssE. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X | rewrite G19; reflexivity]
                       | intros X; discriminate X | rewrite G20; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + unfold stkE, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2u. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; apply Hpres; lia|]. unfold ck.
      apply Forall_cons; [apply (fm_chunk_word E _ _ 0 (getr regs0 20) 32 E32); replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact F1|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 8 (getr regs0 19) 33 E33); replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact F2|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 16 (getr regs0 18) 34 E34); replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact F3|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 24 (getr regs0 9) 35 E35); replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact F4|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 32 (getr regs0 8) 36 E36); replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact F5|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 40 (getr regs0 1) 37 E37); replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact F6|].
      apply Forall_nil.
    + unfold fileE, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E8u. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; exact (proj1 (Hfb (res + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite Z.add_0_r. exact (HZ i Hi).
    + unfold modeR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_MODE; lia|]. split; [unfold FM_MODE; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_MODE 1%N (SLit 114) 114); [reflexivity | cbn; lia | cbn; lia | exact VMODE].
    + unfold thrR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_THR; lia|]. split; [unfold FM_THR; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_THR 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact VTHR].
    + unfold nlR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_NL; lia|]. split; [unfold FM_NL; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_NL 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact VNL].
    + unfold headR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_HEAD; lia|]. split; [unfold FM_HEAD; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_HEAD 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact VHEAD].
  - apply pairwise_disjoint_of_extents. unfold stkE, fileE, modeR, thrR, nlR, headR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2u, E8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold FM_MODE, FM_THR, FM_NL, FM_HEAD in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2u, E8u, E9. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
eapply (SRr_run_to_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL FM_HEADST E ssE eE _ _ STK sp0 FPT
  ly S W0 mem0 md0 [] ly2 S2 md 1 Q HS r_E I HJ).
{ unfold ssE. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off E stkE _ STK sp0 FPT (ablocks B ly S) (ablocks B ly2 S2) ly2 [] 2 (-48));
    [reflexivity | rewrite E2u; lia | cbn [YP09.r_wlo stkE]; rewrite FS; lia | cbn [YP09.r_whi stkE]; lia |].
  eapply (awr_ok_cons_tmp E fileE _ STK sp0 FPT (ablocks B ly S) (ablocks B ly2 S2) ly2 [] 8 res SRC_FILE_BLOCK);
    [reflexivity | exact E8u | exact Hblk2 | exact Hnew | cbn; lia | cbn [YP09.r_whi fileE]; change (req_size SRC_FILE_BLOCK) with 1304; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eE ms1 HS1 eq_refl).
assert (CV : forall off (n : N) v, chunk_at eE 1 off n v = true -> Z.of_N n <= 8 ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (res + off) (N.to_nat n) (bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N n))).
{ intros off n v Hc Hn. pose proof (fm_chunk_val E eE (w_H W) ms1 1 off n v 8 HS1 Hc eq_refl Hn) as V.
  rewrite E8u in V. exact V. }
assert (CZ : forall off len o (n : nat), zchunk_at eE 1 off len = true -> off <= o -> o + Z.of_nat n <= off + len ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (res + o) n 0).
{ intros off len o n Hc H1 H2. pose proof (fm_zchunk_val E eE (w_H W) ms1 1 off len 8 o n HS1 Hc eq_refl H1 H2) as V.
  rewrite E8u in V. exact V. }
assert (LV : forall off (n : N) z, chunk_at eE 1 off n (SLit z) = true -> Z.of_N n <= 8 -> 0 <= z < 2 ^ 64 ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (res + off) (N.to_nat n) (z mod 2 ^ (8 * Z.of_N n))).
{ intros off n z Hc Hn Hz. pose proof (CV off n (SLit z) Hc Hn) as V. cbn [sv_denot] in V.
  rewrite unsigned_lit_small in V by exact Hz. exact V. }
refine (K (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) HJ1 (with_vm_backing_same md mat1)
  _ _ _ _ _ _ _ _ _ _ _ _).
- fm_lit E eE HS1 FM_HEAD.
- rewrite (fm_reg_of E eE _ ms1 2%bv (SOff 2 32) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2u.
  unfold w64. f_equal; lia.
- rewrite (fm_reg_of E eE _ ms1 8%bv (SOff 8 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E8u, Z.add_0_r.
  reflexivity.
- rewrite (fm_reg_of E eE _ ms1 9%bv (SOff 35 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E35, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (fm_reg_of E eE _ ms1 18%bv (SOff 34 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E34, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (fm_reg_of E eE _ ms1 19%bv (SOff 33 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E33, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (fm_reg_of E eE _ ms1 20%bv (SOff 32 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E32, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- exact (fm_keep_of E eE _ _ regs _ HS1 HE ltac:(vm_compute; reflexivity)).
- pose proof (fm_chunk_val E eE (w_H W) ms1 0 32 8 (SOff 36 0) 2 HS1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia)) as V.
  rewrite E2u, (fm_soff0 E 36 (getr regs0 8) E36) in V. replace (sp0 - 48 + 32) with (sp0 - 16) in V by lia. exact V.
- pose proof (fm_chunk_val E eE (w_H W) ms1 0 40 8 (SOff 37 0) 2 HS1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia)) as V.
  rewrite E2u, (fm_soff0 E 37 (getr regs0 1) E37) in V. replace (sp0 - 48 + 40) with (sp0 - 8) in V by lia. exact V.
- unfold fm_file.
  split; [exact (LV 0 4%N 8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 4 20 8 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 4 20 16 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 24 8%N PMCLOSE ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold PMCLOSE; lia))|].
  split; [exact (CZ 32 32 32 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 32 32 40 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 32 32 48 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 32 32 56 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 64 8%N (symaddr Symbols.Asan.s_mread) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 72 8%N (symaddr Symbols.Asan.s_mwrite) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 80 8%N PMSEEK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold PMSEEK; lia))|].
  split; [pose proof (CV 88 8%N (SOff 8 280) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_off_val E 8 280 res E8u ltac:(lia)) in V; exact V|].
  split; [exact (LV 96 8%N 1024 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 104 8 104 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 112 8%N 0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 120 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 124 16 136 4%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 140 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 144 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [pose proof (CV 152 8%N (SOff 8 232) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_off_val E 8 232 res E8u ltac:(lia)) in V; exact V|].
  split; [exact (CZ 160 80 168 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 160 80 232 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [pose proof (CV 240 8%N (SOff 18 0) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_soff0 E 18 (getr regs 18) E18) in V; exact V|].
  split; [pose proof (CV 248 8%N (SOff 18 0) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_soff0 E 18 (getr regs 18) E18) in V; exact V|].
  split; [pose proof (CV 256 8%N (SOff 9 0) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_soff0 E 9 (getr regs 9) E9) in V; exact V|].
  exact (LV 264 4%N 114 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
- intros a Ha H1 H2. apply (fm_mb_frame E (ss_mem ssE) _ _ a HFr1 Ha). unfold ssE. cbn [ss_mem]. apply fm_nwr_all.
  repeat (apply Forall_cons; [unfold stkE, fileE, modeR, thrR, nlR, headR; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    rewrite ?E2u, ?E8u; lia|]). apply Forall_nil.
Qed.

(* 5.12 musl's open-file-list head is a writable image cell (.bss), MEASURED on the image (WFclose.v's
   wf_ofl_img_facts / wf_ofl_writable for this walk). *)
Lemma fm_head_writable : forall (m : word -> option byte) o, 0 <= o < 8 -> writable_at tfibsegs m (FM_HEAD + o).
Proof.
intros m o Ho.
assert (Hw : YP08.img_writable_ok tfibsegs (FM_HEAD + o) = true).
{ assert (C : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7] -> YP08.img_writable_ok tfibsegs (FM_HEAD + j) = true).
  { intros j Hj. cbn [In] in Hj. repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]). destruct Hj. }
  apply C. cbn [In]. lia. }
unfold YP08.img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (FM_HEAD + o))); [discriminate | discriminate Hw].
Qed.

(* 5.13 Phase F: the head store `sd s0,0(a0)` (head = f), __ofl_unlock / __unlock (lock word 0), __ofl_add's
   epilogue and ret. Run plainly (the head is no awr_byte); the journal is rebuilt by fm_head_journal. *)
Lemma fm_F : forall (W W0 : world tfibsegs) ly S mem0 md0 lyc Sc sp0 regs mem md k s0v rav
    (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem md k ->
  getr regs 10 = w64 FM_HEAD -> spZ regs = sp0 - 16 ->
  0 <= s0v < 2 ^ 64 -> 0 <= rav < 2 ^ 64 -> YK0s.ret_ok (w64 rav) ->
  val_mem tfibsegs (rd W mem) (sp0 - 16) 8 s0v -> val_mem tfibsegs (rd W mem) (sp0 - 8) 8 rav ->
  val_mem tfibsegs (rd W mem) FM_LOCK 4 0 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] lyc Sc W mem1 md1 k ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 rav -> getr regs1 8 = w64 s0v -> getr regs1 2 = w64 sp0 -> getr regs1 10 = getr regs 8 ->
     (forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
        getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     val_mem tfibsegs (rd W mem1) FM_HEAD 8 (bv_unsigned (getr regs 8)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (FM_HEAD <= a < FM_HEAD + 8) ->
        mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a) ->
     Q W (mkCfg (mkst regs1 (w64 rav) mem1 (seg_rom tfibsegs)) md1)) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_HEADST regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 lyc Sc sp0 regs mem md k s0v rav Q HJ G10 Hsp Hs0 Hrav Hret V16 V8 VL K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo.
remember (Ereg regs [w64 s0v; w64 rav]) as E eqn:HE.
assert (E2u : bv_unsigned (ew E 2) = sp0 - 16) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = getr regs 8) by (rewrite HE; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E32 : ew E 32 = w64 s0v) by (rewrite HE; reflexivity).
assert (E33 : ew E 33 = w64 rav) by (rewrite HE; reflexivity).
unfold cfg_at. change (w64 FM_HEADST) with (Z_to_bv 64 (ss_pc ssF)).
assert (HS : st_ok tfibsegs E ssF (restrict (w_H W) (mkst regs (Z_to_bv 64 (ss_pc ssF)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssF. cbn [ss_pc]. rewrite HE. apply (entry_st_ok_full tfibsegs); try rewrite <- HE.
  - apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X | rewrite G10; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold stkF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. unfold ck.
      apply Forall_cons; [apply (fm_chunk_word E _ _ 0 (w64 s0v) 32 E32); unfold w64; rewrite unsigned_lit_small by exact Hs0;
        replace (sp0 - 16 + 0) with (sp0 - 16) by lia; exact V16|].
      apply Forall_cons; [apply (fm_chunk_word E _ _ 8 (w64 rav) 33 E33); unfold w64; rewrite unsigned_lit_small by exact Hrav;
        replace (sp0 - 16 + 8) with (sp0 - 8) by lia; exact V8|].
      apply Forall_nil.
    + unfold headW, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_HEAD; lia|]. split; [unfold FM_HEAD; lia|].
      split; [|apply Forall_nil].
      intros o Ho. replace (0 + o) with (FM_HEAD + (o - FM_HEAD)) by lia. apply fm_head_writable. lia.
    + unfold lockR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_LOCK; lia|]. split; [unfold FM_LOCK; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_LOCK 4%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact VL].
  - apply pairwise_disjoint_of_extents. unfold stkF, headW, lockR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold FM_HEAD, FM_LOCK. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2u.
    change (2 ^ 4) with 16. repeat split; lia. }
eapply (SRr_run_gen tfibsegs fm_tbl fm_tbl_ok fm_wx W FUEL E ssF eF _ _ md Q HS r_F).
intros ms1 mat1 HS1 HF1 HFr1. cbn [ms_mem mkst] in HF1, HFr1.
eapply (SRr_ret_at tfibsegs fm_tbl fm_tbl_ok fm_wx W E eF ms1 _ Q HS1 eq_refl ltac:(vm_compute; reflexivity)).
intros mat2.
assert (R1 : getr (ms_regs ms1) 1 = w64 rav).
{ rewrite (fm_reg_of E eF _ ms1 1%bv (SOff 33 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E33, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
rewrite R1. unfold YK0s.ret_ok in Hret. rewrite Hret.
assert (VH : val_mem tfibsegs (rd W (ms_mem ms1)) FM_HEAD 8 (bv_unsigned (getr regs 8))).
{ pose proof (fm_chunk_val0 E eF (w_H W) ms1 1 FM_HEAD 8 (SOff 8 0) HS1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia)) as V.
  rewrite (fm_soff0 E 8 (getr regs 8) E8) in V. exact V. }
assert (MF : same_but_materialized md
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat1 md)) mat2 (with_vm_backing (m_vm_lazy md) mat1 md))).
{ eapply same_but_materialized_trans; apply with_vm_backing_same. }
apply (K (ms_regs ms1) (ms_mem ms1) _).
- apply (fm_head_journal sp0 ly S W0 W mem0 md0 lyc Sc mem md k (ms_mem ms1) _ HJ).
  + intros x Hx. apply HF1. intros (r & Hin & Hr). unfold ssF in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi stkF headW lockR base_val] in Hr;
      [lia | apply Hx; exact Hr | lia].
  + intros a Ha. unfold aview. replace a with (FM_HEAD + Z.of_nat (Z.to_nat (a - FM_HEAD))) by lia.
    rewrite (VH (Z.to_nat (a - FM_HEAD)) ltac:(lia)). discriminate.
  + exact MF.
- exact MF.
- exact R1.
- rewrite (fm_reg_of E eF _ ms1 8%bv (SOff 32 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E32, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (fm_reg_of E eF _ ms1 2%bv (SOff 2 16) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2u.
  unfold w64. f_equal; lia.
- rewrite (fm_reg_of E eF _ ms1 10%bv (SOff 8 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E8, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- intros r Hr. apply (fm_reg_kept E eF _ ms1 regs [w64 s0v; w64 rav] r HS1 HE).
  + cbn [In] in Hr. lia.
  + cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr.
- exact VH.
- intros a Ha Hn. apply (fm_mb_frame E (ss_mem ssF) _ _ a HFr1 Ha). unfold ssF. cbn [ss_mem]. apply fm_nwr_all.
  repeat (apply Forall_cons; [unfold stkF, headW, lockR; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    rewrite ?E2u; lia|]). apply Forall_nil.
Qed.

(* 5.14 The post's stream from the FILE fields. *)
Lemma fm_unbuf : forall m f b (C : list Z),
  0 < f -> f mod 16 = 0 -> 0 < b -> (f + SRC_FILE_BLOCK <= b \/ b + Z.of_nat (length C) <= f) ->
  Z.of_nat (length C) < 2 ^ 63 -> b + Z.of_nat (length C) <= 2 ^ 64 -> b < 2 ^ 64 ->
  bytes_ok C -> garr8 tfibsegs m b C ->
  fm_file m f (w64 b) (w64 (Z.of_nat (length C))) ->
  asrc_stdio_env tfibsegs pcap_KS m -> val_mem tfibsegs m (as_ofl_head pcap_KS) 8 f ->
  asource_unbuffered tfibsegs pcap_KS m f b C 0.
Proof.
intros m f b C Hf0 Hf16 Hb0 Hdisj Hn63 Hbn Hb64 Hbok HC HF HENV HHD.
pose proof HF as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 &
  V136 & V140 & V144 & V152 & V168 & V232 & V240 & V248 & V256 & V264).
unfold w64 in V240, V248, V256.
rewrite unsigned_lit_small in V240, V248 by lia. rewrite unsigned_lit_small in V256 by lia.
rewrite Z.add_0_r in V0.
assert (HW0 : source_window tfibsegs m f []) by (left; split; [reflexivity | split; [exact V8 | exact V16]]).
split; [|exact HW0].
exists [], 0, 8, 0. cbv zeta. cbn [length Z.of_nat].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hn63|]. split; [exact Hbn|]. split; [lia|].
split; [reflexivity|]. split; [exact Hbok|]. split; [exact HC|].
split.
{ unfold source_static.
  split; [exact V24|]. split; [exact V64|]. split; [exact V72|]. split; [exact V80|]. split; [exact V88|].
  split; [exact V96|]. split; [exact V240|]. split; [exact V248|]. split; [exact V256|]. split; [exact V264|].
  split; [exact V152|]. split; [exact V32|]. split; [exact V40|]. split; [exact V48|]. split; [exact V56|].
  split; [exact V104|]. split; [exact V112|]. split; [exact V168|]. split; [exact V120|]. split; [exact V140|].
  split; [exact V144|]. split; [lia|]. split; [exact Hf16|]. split; [lia|]. exact Hdisj. }
split; [exact HW0|].
split; [split; [exact V0 | left; reflexivity]|].
split; [intros H; discriminate H|].
split; [split; [exact V136 | left; reflexivity]|].
split; [exact V232|]. split; [exact HENV|]. split; [exact HHD|]. lia.
Qed.

(* 5.15 Low image memory (below 0x600000) carries the stdio environment. *)
Lemma fm_env_low : forall m m', asrc_stdio_env tfibsegs pcap_KS m ->
  (forall a, 0 <= a < 0x600000 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> asrc_stdio_env tfibsegs pcap_KS m'.
Proof.
intros m m' (H1 & H2 & H3 & H4 & H5 & (cv & Hcv & H6)) Hk.
assert (FR : forall a, (a = as_threaded pcap_KS \/ a = as_need_locks pcap_KS \/
    (as_ofl_lock pcap_KS <= a < as_ofl_lock pcap_KS + 4) \/ (as_mode pcap_KS <= a < as_mode pcap_KS + 3) \/
    (as_rwa pcap_KS <= a < as_rwa pcap_KS + 4) \/ (as_canary pcap_KS <= a < as_canary pcap_KS + 8)) ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a).
{ intros a Ha. apply Hk. revert Ha. pks. lia. }
split; [eapply fm_vm_fr; [|exact H1]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply fm_vm_fr; [|exact H2]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply fm_vm_fr; [|exact H3]; intros x Hx; apply FR; simpl Z.of_nat in Hx; lia|].
split; [eapply garr8_frame; [exact H4|]; intros x Hx; apply FR; unfold src_mode_Z in Hx; cbn [length app] in Hx; simpl Z.of_nat in Hx; lia|].
split; [eapply garr8_frame; [exact H5|]; intros x Hx; apply FR; unfold src_modeset_Z in Hx; cbn [length app] in Hx; simpl Z.of_nat in Hx; lia|].
exists cv. split; [exact Hcv|]. eapply fm_vm_fr; [|exact H6]. intros x Hx. apply FR. simpl Z.of_nat in Hx. lia.
Qed.

Lemma fm_vm1 : forall m a v, mbyte tfibsegs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem tfibsegs m a 1 v.
Proof.
intros m a v H Hv k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, H. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* 5.16 Small transport helpers. *)
Lemma fm_sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof.
intros m m' H. pose proof (same_but_materialized_frame m m' H) as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & F2 & _).
exact (conj F1 F2).
Qed.
Lemma fm_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
Lemma fm_w64_un : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma fm_av_mb : forall (W W' : world tfibsegs) m m' a,
  mbyte tfibsegs (rd W' m') a = mbyte tfibsegs (rd W m) a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a.
Proof. intros W W' m m' a H. unfold aview. rewrite H. reflexivity. Qed.
Lemma fm_kl : forall (P : Z -> Prop) (r0 r1 : bvmap 5 word) r (rb : bv 5),
  (forall r, P r -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) -> P r -> Z_to_bv 5 r = rb -> getr r1 rb = getr r0 rb.
Proof. intros P r0 r1 r rb H Hp <-. exact (H r Hp). Qed.
Ltac fmP := first [unfold acallee_saved; lia | unfold KEPTS; cbn [In]; tauto | cbn [In]; tauto].
Ltac fmB := apply bv_eq; reflexivity.

Lemma fm_fresh : forall ly S ly2 S2 (W : world tfibsegs) mem md res,
  AR tfibsegs B ly2 S2 W mem md -> ablocks B ly2 S2 = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] ->
  ~ In (res, SRC_FILE_BLOCK) (ablocks B ly S).
Proof.
intros ly S ly2 S2 W mem md res HAR Hab Hin.
assert (Hb : In (res, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W mem md res SRC_FILE_BLOCK HAR Hb) as (_ & _ & _ & _ & _ & Hdisj & _).
rewrite Hab, map_app in Hdisj. cbn [map fst snd] in Hdisj.
pose proof (YG0s.pairwise_In _ _ (res, req_size SRC_FILE_BLOCK) (res, req_size SRC_FILE_BLOCK) _ _ eq_refl Hdisj
  ltac:(apply in_map_iff; exists (res, SRC_FILE_BLOCK); split; [reflexivity | exact Hin]) ltac:(left; reflexivity)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. change (req_size SRC_FILE_BLOCK) with 1304 in HD. lia.
Qed.

Lemma fm_env_mode : forall m, asrc_stdio_env tfibsegs pcap_KS m -> val_mem tfibsegs m FM_MODE 1 114.
Proof.
intros m (_ & _ & _ & Emode & _).
pose proof (fm_garr8_byte _ (as_mode pcap_KS) _ 0 Emode ltac:(cbn; lia)) as X.
change (as_mode pcap_KS + Z.of_nat 0) with FM_MODE in X. change (nth 0 (src_mode_Z ++ [0]) 0) with 114 in X.
apply fm_vm1; [exact X | lia].
Qed.

(* 5.17 The tail: from memset's return to the contract's post. *)
Lemma fm_tail : forall (W W2 : world tfibsegs) ly S mem md ly2 S2 regs regsM memM mdM res b C,
  AJ STK (spZ regs) FPT ly S W mem md [] ly2 S2 W2 memM mdM 1 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] ->
  mo_le MT S S2 (mo_malloc MT SRC_FILE_BLOCK) ->
  m_fds mdM = m_fds md -> m_fs mdM = m_fs md ->
  YK0s.ret_ok (getr regs 1) ->
  getr regsM 2 = w64 (spZ regs - 48) -> getr regsM 8 = w64 res -> getr regsM 9 = w64 b ->
  getr regsM 18 = w64 (Z.of_nat (length C)) -> getr regsM 19 = w64 FM_MODE -> getr regsM 20 = w64 0 ->
  fm_keep regs regsM ->
  fm_frame (spZ regs) (rd W2 memM) regs ->
  (forall i, 0 <= i < 272 -> mbyte tfibsegs (rd W2 memM) (res + i) = Some (Z_to_bv 8 0)) ->
  val_mem tfibsegs (rd W2 memM) FM_HEAD 8 0 ->
  asrc_stdio_env tfibsegs pcap_KS (rd W mem) ->
  In (b, Z.of_nat (length C)) (ablocks B ly S) -> garr8 tfibsegs (rd W mem) b C -> bytes_ok C ->
  Z.of_nat (length C) < 2 ^ 26 ->
  SRr tfibsegs W2 (cfg_at tfibsegs FM_RA4 regsM memM mdM)
    (apost_base tfibsegs B STK FPT regs ly S W mem md 1 (rfmemopen_post tfibsegs B pcap_KS MT b C ly S md)).
Proof.
intros W W2 ly S mem md ly2 S2 regs regsM memM mdM res b C JM Hab2 Hmo2 Fd Fs Hra M2 M8 M9 M18 M19 M20 MK MFR MZ MHD
  HENV0 Hblk HC Hbok Hn26.
set (sp0 := spZ regs) in *.
pose proof JM as (HARM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo.
assert (Hblk2 : In (res, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM res SRC_FILE_BLOCK HARM Hblk2) as (Hf16 & Hf4 & Hfceil & _ & _ & Hfdisj & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil.
assert (Hnew : ~ In (res, SRC_FILE_BLOCK) (ablocks B ly S)) by exact (fm_fresh ly S ly2 S2 W2 memM mdM res HARM Hab2).
assert (HblkB : In (b, Z.of_nat (length C)) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; left; exact Hblk).
destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM b _ HARM HblkB) as (Hb16 & Hb4 & Hbceil & _ & _ & _ & _).
assert (Hbh : b + Z.of_nat (length C) <= alloc_ceiling) by (unfold req_size in Hbceil; destruct (Z.of_nat (length C) =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | lia]).
assert (Hbr : res + 1304 <= b \/ b + Z.of_nat (length C) <= res).
{ rewrite Hab2, map_app in Hfdisj.
  pose proof (YG0s.pairwise_In _ _ (b, req_size (Z.of_nat (length C))) (res, req_size SRC_FILE_BLOCK) _ _ eq_refl Hfdisj
    ltac:(apply in_map_iff; exists (b, Z.of_nat (length C)); split; [reflexivity | exact Hblk])
    ltac:(cbn [map]; left; reflexivity)) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. change (req_size SRC_FILE_BLOCK) with 1304 in HD. unfold req_size in HD.
  destruct (Z.of_nat (length C) =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | lia]. }
assert (HENVM : asrc_stdio_env tfibsegs pcap_KS (rd W2 memM)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JM HENV0).
pose proof HENVM as (EThr & ENl & _).
refine (fm_E W2 W ly S mem md ly2 S2 sp0 regsM regs memM mdM res _ JM Hblk2 Hnew _ M8 _ M19 M20 MFR MZ
  (fm_env_mode _ HENVM) EThr ENl MHD _).
- unfold spZ. rewrite M2. apply fm_w64u. lia.
- rewrite M9, fm_w64u by lia. lia.
- intros regs1 mem1 md1 J1 SB1 E10 E2 E8 E9 E18 E19 E20 EK E16 E8' EF EFR.
  assert (HENV1 : asrc_stdio_env tfibsegs pcap_KS (rd W2 mem1)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 HENV0).
  pose proof HENV1 as (_ & _ & ELock & _).
  refine (fm_F W2 W ly S mem md ly2 S2 sp0 regs1 mem1 md1 1 (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 1)) _
    J1 E10 _ (u64_range _) (u64_range _) _ E16 E8' ELock _).
  + unfold spZ. rewrite E2. apply fm_w64u. lia.
  + rewrite fm_w64_un. exact Hra.
  + intros regsF memF mdF JF SBF F1 F8 F2 F10 FK FVH FFR.
    pose proof JF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & JF2 & _).
    unfold apost_base. exists ly2, S2, regsF, memF, mdF.
    split; [rewrite fm_w64_un; reflexivity|].
    split; [exact JF|].
    split.
    { intros r Hr. unfold acallee_saved in Hr.
      assert (KP : fm_keep regs regs1) by exact (fm_keep_trans _ _ _ MK EK).
      assert (Hcase : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ In r [3; 4; 21; 22; 23; 24; 25; 26; 27])
        by (cbn [In]; lia).
      destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | Hin]]]]]].
      - replace (Z_to_bv 5 2) with (2%bv : bv 5) by fmB. rewrite F2. apply fm_w64_un.
      - replace (Z_to_bv 5 8) with (8%bv : bv 5) by fmB. rewrite F8. apply fm_w64_un.
      - rewrite (FK 9 ltac:(cbn [In]; tauto)). replace (Z_to_bv 5 9) with (9%bv : bv 5) by fmB. exact E9.
      - rewrite (FK 18 ltac:(cbn [In]; tauto)). replace (Z_to_bv 5 18) with (18%bv : bv 5) by fmB. exact E18.
      - rewrite (FK 19 ltac:(cbn [In]; tauto)). replace (Z_to_bv 5 19) with (19%bv : bv 5) by fmB. exact E19.
      - rewrite (FK 20 ltac:(cbn [In]; tauto)). replace (Z_to_bv 5 20) with (20%bv : bv 5) by fmB. exact E20.
      - rewrite (FK r ltac:(cbn [In] in Hin |- *; tauto)). exact (KP r Hin). }
    pose proof (fm_sbm_fds _ _ SB1) as [Fd1 Fs1]. pose proof (fm_sbm_fds _ _ SBF) as [FdF FsF].
    exists res.
    split; [rewrite F10; exact E8|].
    split; [exact Hmo2|].
    split; [exact Hf4|].
    split; [exact Hf16|].
    split; [exact Hab2|].
    split; [| split; [rewrite FdF, Fd1; exact Fd | rewrite FsF, Fs1; exact Fs]].
    assert (HIMGH : forall a, FM_HEAD <= a < FM_HEAD + 8 -> ~ (res <= a < res + 272)).
    { intros a Ha Hb.
      destruct (asil_env _ _ _ _ ASIL a ltac:(pks; unfold FM_HEAD in Ha; lia)) as (Hi & _ & _).
      apply (blk_img tfibsegs B LAWS ly2 S2 W2 memM mdM res SRC_FILE_BLOCK a HARM Hblk2);
        [change (req_size SRC_FILE_BLOCK) with 1304; lia | exact Hi]. }
    apply fm_unbuf.
    * lia.
    * exact Hf16.
    * lia.
    * unfold SRC_FILE_BLOCK. exact Hbr.
    * lia.
    * lia.
    * lia.
    * exact Hbok.
    * eapply garr8_frame; [exact HC|]. intros a Ha. apply mbyte_of_aview.
      replace a with (b + (a - b)) by lia.
      apply (JF2 b (Z.of_nat (length C)) (a - b) Hblk HblkB).
      { unfold req_size. destruct (Z.of_nat (length C) =? 0) eqn:E0; [apply Z.eqb_eq in E0|]; lia. }
      { intros (r & Hr & Hra'). destruct Hr as [<- | []]. cbn in Hra'. lia. }
    * rewrite <- M9, <- M18. eapply fm_file_kept; [exact EF|].
      intros a Ha. apply FFR; [lia|]. intros Hh. exact (HIMGH a Hh Ha).
    * exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JF HENV0).
    * rewrite E8, fm_w64u in FVH by lia. exact FVH.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 6. THE CONTRACT, on pcap's ASan image, at fmemopen's entry 0x8e870, ra 0x8e90c, window          *)
(*    [0x10350, 0x10370).                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)
Theorem rfmemopen_contract_pcap :
  @rfmemopen_contract fx rc SK tfibsegs B pcap_KS MT CTX PFMEMOPEN FM_MALLOC_RA FM_MC_LO FM_MC_HI.
Proof.
intros RULE W ly S regs mem md ch b n C Hpre.
destruct Hpre as (HFN & G10 & G11 & G12 & (HENV0 & HHD0) & Hn & Hn26 & Hblk & HC & Hbok & HMC & Hnev & Hlive & Hmo
  & Hsp & Huni0 & Huni).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo.
subst n.
set (sp0 := spZ regs) in *.
destruct (al_blocks _ _ LAWS ly S W mem md b _ HAR Hblk) as (Hb16 & Hb4 & Hbceil & _).
assert (Hbh : b + Z.of_nat (length C) <= alloc_ceiling) by (unfold req_size in Hbceil; destruct (Z.of_nat (length C) =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | lia]).
assert (HJ0 : AJ STK sp0 FPT ly S W mem md [] ly S W mem md 0)
  by (eapply ajournal_init; first [exact HFN | exact LAWS | exact fm_segs_low]).
pose proof mc_bounds as [MB1 MB2].
(* A: entry to strchr(mode, '+'). *)
apply (fm_A W W ly S mem md regs mem md _ HJ0 G12).
intros regs1 mem1 md1 J1 SB1 A1 A2 A10 A11 A8 A9 A18 A19 A20 AK AFR AMB.
assert (HENV1 : asrc_stdio_env tfibsegs pcap_KS (rd W mem1)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 HENV0).
pose proof J1 as (HAR1 & _).
assert (HMC1 : mconsts_view W mem1).
{ intros a Ha. rewrite MB1, MB2 in Ha. rewrite (fm_av_mb W W mem mem1 a (AMB a ltac:(lia) ltac:(lia))).
  apply HMC. unfold FM_MC_LO, FM_MC_HI. lia. }
assert (SP1 : spZ regs1 = sp0 - 48) by (unfold spZ; rewrite A2; apply fm_w64u; lia).
apply (fm_strchr_step FM_MODE 43 0 W W ly S mem md regs1 mem1 md1 sp0 _ ltac:(right; left; reflexivity) J1 SP1).
{ rewrite A1. apply AE2y.ret_ok_lit; [unfold FM_RA1; lia | reflexivity]. }
{ exact A10. }
{ exact A11. }
{ exact (fm_cells ly S W mem1 md1 HAR1 HENV1). }
{ exact (fm_rwa_img W mem1 HENV1). }
{ exact HMC1. }
intros regs2 mem2 md2 J2 SB2 P10 P1 P2 PK2 PAV.
unfold SC_WIN in PAV.
replace (raZ regs1) with FM_RA1 by (unfold raZ; rewrite A1; symmetry; apply fm_w64u; unfold FM_RA1; lia).
(* B: strchr returned 0; to strchr("rwa", 'r'). *)
assert (HENV2 : asrc_stdio_env tfibsegs pcap_KS (rd W mem2)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 HENV0).
apply (fm_B W W ly S mem md sp0 regs2 mem2 md2 _ J2 P10).
{ rewrite (fm_kl _ _ _ 19 19%bv PK2 ltac:(fmP) ltac:(fmB)). exact A19. }
{ exact (fm_env_mode _ HENV2). }
intros regs3 mem3 md3 J3 SB3 B1 B10 B11 B19 B20 B2 B8 B9 B18 BK BMB.
assert (HENV3 : asrc_stdio_env tfibsegs pcap_KS (rd W mem3)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J3 HENV0).
pose proof J3 as (HAR3 & _).
assert (SP3 : spZ regs3 = sp0 - 48) by (unfold spZ; rewrite B2, P2; exact SP1).
assert (HMC3 : mconsts_view W mem3).
{ intros a Ha. rewrite MB1, MB2 in Ha. rewrite (fm_av_mb W W mem2 mem3 a (BMB a ltac:(lia))).
  rewrite PAV by lia. exact (HMC1 a ltac:(rewrite MB1, MB2; lia)). }
apply (fm_strchr_step FM_RWA 114 FM_RWA W W ly S mem md regs3 mem3 md3 sp0 _ ltac:(left; reflexivity) J3 SP3).
{ rewrite B1. apply AE2y.ret_ok_lit; [unfold FM_RA2; lia | reflexivity]. }
{ exact B10. }
{ exact B11. }
{ exact (fm_cells ly S W mem3 md3 HAR3 HENV3). }
{ exact (fm_rwa_img W mem3 HENV3). }
{ exact HMC3. }
intros regs4 mem4 md4 J4 SB4 T10 T1 T2 TK TAV.
unfold SC_WIN in TAV.
replace (raZ regs3) with FM_RA2 by (unfold raZ; rewrite B1; symmetry; apply fm_w64u; unfold FM_RA2; lia).
(* C: strchr returned "rwa"; to the malloc call. *)
apply (fm_C W W ly S mem md sp0 regs4 mem4 md4 _ J4 T10).
{ rewrite (fm_kl _ _ _ 9 9%bv TK ltac:(fmP) ltac:(fmB)), B9, (fm_kl _ _ _ 9 9%bv PK2 ltac:(fmP) ltac:(fmB)), A9, G10.
  rewrite fm_w64u by lia. lia. }
intros regs5 mem5 md5 J5 SB5 C1' C10 C2 C8 C9 C18 C19 C20 CK CMB.
assert (KP5 : fm_keep regs regs5).
{ eapply fm_keep_trans; [|exact CK]. eapply fm_keep_trans; [|exact (fm_keep_kepts _ _ TK)].
  eapply fm_keep_trans; [|exact BK]. eapply fm_keep_trans; [exact AK | exact (fm_keep_kepts _ _ PK2)]. }
assert (SP5 : spZ regs5 = sp0 - 48) by (unfold spZ; rewrite C2, T2; exact SP3).
assert (S08 : getr regs5 8 = getr regs 8).
{ rewrite C8, (fm_kl _ _ _ 8 8%bv TK ltac:(fmP) ltac:(fmB)), B8, (fm_kl _ _ _ 8 8%bv PK2 ltac:(fmP) ltac:(fmB)). exact A8. }
(* the malloc call: amalloc04_rule through PaJournalFs.amalloc04_sub_fs. *)
pose proof (ts_code B TL) as TC.
unfold cfg_at. replace (w64 FM_MALLOC) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite TC; reflexivity).
eapply SRr_bind.
{ apply (PaJournalFs.amalloc04_sub_fs SK tfibsegs B LAWS fm_segs_low MT RULE W regs5 mem5 STK sp0 FPT ly S W mem md [] ly S
    md5 0 SRC_FILE_BLOCK (-48) (w64 FM_MALLOC_RA) ch J5 C10).
  - unfold SRC_FILE_BLOCK, MALLOC_MAX. lia.
  - exact Hlive.
  - rewrite SP5. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. rewrite FS. lia.
  - rewrite (fm_kl _ _ _ 3 3%bv KP5 ltac:(fmP) ltac:(fmB)). exact Hgp.
  - rewrite (fm_kl _ _ _ 4 4%bv KP5 ltac:(fmP) ltac:(fmB)). exact Htp.
  - exact C1'.
  - apply AE2y.ret_ok_lit; [unfold FM_MALLOC_RA; lia | reflexivity].
  - lia.
  - apply (achain_chain_pre ly _ sp0 (s0Z regs) ch regs5).
    + apply (achain_kept ly (aview tfibsegs (w_H W) mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
      intros a Ha. pose proof J5 as (_ & _ & _ & _ & _ & _ & _ & _ & J5F1 & _). apply J5F1; [lia|]. rewrite FS. lia.
    + rewrite SP5. lia.
    + unfold s0Z. rewrite S08. reflexivity.
    + unfold raZ. rewrite C1', fm_w64u; unfold FM_MALLOC_RA; lia.
  - rewrite call_trace_of_spine.
    replace (raZ regs5) with FM_MALLOC_RA by (unfold raZ; rewrite C1'; symmetry; apply fm_w64u; unfold FM_MALLOC_RA; lia).
    exact (Huni _ Hsp).
  - exact Hmo. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs6 & mem6 & md6 & res & -> & J6 & HPR6 & U10 & Hfr6 & Hres & Hab2 & HCK & Hmo2
  & Fd6 & Fs6).
pose proof HCK as (K1 & _ & K3 & _).
unfold ASTACK in K1.
pose proof J6 as (HAR6 & _).
assert (Hblk6 : In (res, SRC_FILE_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem6 md6 res SRC_FILE_BLOCK HAR6 Hblk6) as (Hf16 & Hf4 & Hfceil & Hfapp & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil, Hfapp.
assert (Hnew : ~ In (res, SRC_FILE_BLOCK) (ablocks B ly S)) by exact (fm_fresh ly S ly2 S2 W2 mem6 md6 res HAR6 Hab2).
unfold aregs_preserved in HPR6.
change (mkCfg (mkst regs6 (w64 FM_MALLOC_RA) mem6 (seg_rom tfibsegs)) md6) with (cfg_at tfibsegs FM_MALLOC_RA regs6 mem6 md6).
(* D: malloc returned res >= 4096 (the NULL arm 0x8e910 is refuted here); to the memset call. *)
apply (fm_D W2 W ly S mem md ly2 S2 sp0 regs6 mem6 md6 1 _ J6).
{ rewrite U10, fm_w64u by lia. lia. }
{ rewrite U10, fm_w64u by lia. exact Hf16. }
intros regs7 mem7 md7 J7 SB7 D1 D10 D8 D11 D12 D2 D9 D18 D19 D20 DK DMB.
pose proof J7 as (HAR7 & _).
assert (SP7 : spZ regs7 = sp0 - 48)
  by (unfold spZ; rewrite D2, (fm_kl _ _ _ 2 2%bv HPR6 ltac:(fmP) ltac:(fmB)); exact SP5).
assert (KP7 : fm_keep regs regs7) by (eapply fm_keep_trans; [eapply fm_keep_trans; [exact KP5 | exact (fm_keep_pres _ _ HPR6)] | exact DK]).
(* memset(res, 0, 272) through YC85G.aj_intrin_atS and AINTR. *)
change (cfg_at tfibsegs FM_MEMSET regs7 mem7 md7) with (mkCfg (mkst regs7 (Z_to_bv 64 FM_MEMSET) mem7 (seg_rom tfibsegs)) md7).
eapply SRr_bind.
{ apply (YC85G.aj_intrin_atS tfibsegs B LAWS fm_segs_low OSet FM_MEMSET AINTR W2 regs7 mem7 STK sp0 FPT ly S W mem md []
    ly2 S2 md7 1 res 0 272 (-48) (w64 FM_RA4) J7).
  - rewrite D10. exact U10.
  - exact D11.
  - exact D12.
  - lia.
  - lia.
  - lia.
  - rewrite SP7. lia.
  - reflexivity.
  - lia.
  - unfold ESTACK. rewrite FS. lia.
  - rewrite (fm_kl _ _ _ 3 3%bv KP7 ltac:(fmP) ltac:(fmB)). exact Hgp.
  - rewrite (fm_kl _ _ _ 4 4%bv KP7 ltac:(fmP) ltac:(fmB)). exact Htp.
  - exact D1.
  - apply AE2y.ret_ok_lit; [unfold FM_RA4; lia | reflexivity].
  - intros a Ha. split.
    + right. right. left. exists res, SRC_FILE_BLOCK. split; [exact Hblk6|]. split; [exact Hnew|].
      change (req_size SRC_FILE_BLOCK) with 1304. lia.
    + unfold ESTACK. lia.
  - clear - Hfapp Hf4 C1. unfold in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem7 md7 res SRC_FILE_BLOCK res 272 HAR7 Hblk6);
      [lia | change (req_size SRC_FILE_BLOCK) with 1304; lia].
  - intros _. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem7 md7 res SRC_FILE_BLOCK res 272 HAR7 Hblk6);
      [lia | change (req_size SRC_FILE_BLOCK) with 1304; lia | lia].
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs8 & mem8 & md8 & -> & J8 & HPR8 & M10 & MZ8 & MFR8 & MPR8 & SB8).
unfold aregs_preserved in HPR8. unfold ESTACK in MFR8.
change (mkCfg (mkst regs8 (w64 FM_RA4) mem8 (seg_rom tfibsegs)) md8) with (cfg_at tfibsegs FM_RA4 regs8 mem8 md8).
(* the frame, the head and the FILE zero bytes after memset. *)
assert (FR : forall a, sp0 - 48 <= a < sp0 -> aview tfibsegs (w_H W2) mem8 a = aview tfibsegs (w_H W) mem1 a).
{ intros a Ha.
  rewrite MFR8 by lia. rewrite (fm_av_mb W2 W2 mem6 mem7 a (DMB a ltac:(lia))).
  rewrite K1 by lia. rewrite (fm_av_mb W W mem4 mem5 a (CMB a ltac:(lia))).
  rewrite TAV by lia. rewrite (fm_av_mb W W mem2 mem3 a (BMB a ltac:(lia))).
  rewrite PAV by lia. reflexivity. }
assert (HD : forall a, FM_HEAD <= a < FM_HEAD + 8 -> aview tfibsegs (w_H W2) mem8 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
  destruct (asil_env _ _ _ _ ASIL a ltac:(pks; unfold FM_HEAD in Ha; lia)) as (Hi & Hns & He).
  rewrite MFR8; [| unfold FM_HEAD in Ha; lia | | unfold FM_HEAD in Ha; lia].
  2: { intros Hb. apply (blk_img tfibsegs B LAWS ly2 S2 W2 mem6 md6 res SRC_FILE_BLOCK a HAR6 Hblk6);
         [change (req_size SRC_FILE_BLOCK) with 1304; lia | exact Hi]. }
  rewrite (fm_av_mb W2 W2 mem6 mem7 a (DMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite K3 by assumption. rewrite (fm_av_mb W W mem4 mem5 a (CMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite TAV by (unfold FM_HEAD in Ha; lia). rewrite (fm_av_mb W W mem2 mem3 a (BMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite PAV by (unfold FM_HEAD in Ha; lia).
  exact (fm_av_mb W W mem mem1 a (AMB a ltac:(unfold FM_HEAD in Ha; lia) ltac:(unfold FM_HEAD in Ha; lia))). }
pose proof (fm_sbm_fds _ _ SB1) as [Fd1 Fs1]. pose proof (fm_sbm_fds _ _ SB2) as [Fd2 Fs2].
pose proof (fm_sbm_fds _ _ SB3) as [Fd3 Fs3]. pose proof (fm_sbm_fds _ _ SB4) as [Fd4 Fs4].
pose proof (fm_sbm_fds _ _ SB5) as [Fd5 Fs5]. pose proof (fm_sbm_fds _ _ SB7) as [Fd7 Fs7].
pose proof (fm_sbm_fds _ _ SB8) as [Fd8 Fs8].
apply (fm_tail W W2 ly S mem md ly2 S2 regs regs8 mem8 md8 res b C J8 Hab2 Hmo2).
- rewrite Fd8, Fd7, Fd6, Fd5, Fd4, Fd3, Fd2, Fd1. reflexivity.
- rewrite Fs8, Fs7, Fs6, Fs5, Fs4, Fs3, Fs2, Fs1. reflexivity.
- exact Hra.
- rewrite (fm_kl _ _ _ 2 2%bv HPR8 ltac:(fmP) ltac:(fmB)), D2, (fm_kl _ _ _ 2 2%bv HPR6 ltac:(fmP) ltac:(fmB)), C2, T2, B2, P2.
  exact A2.
- rewrite (fm_kl _ _ _ 8 8%bv HPR8 ltac:(fmP) ltac:(fmB)), D8. exact U10.
- rewrite (fm_kl _ _ _ 9 9%bv HPR8 ltac:(fmP) ltac:(fmB)), D9, (fm_kl _ _ _ 9 9%bv HPR6 ltac:(fmP) ltac:(fmB)), C9,
    (fm_kl _ _ _ 9 9%bv TK ltac:(fmP) ltac:(fmB)), B9, (fm_kl _ _ _ 9 9%bv PK2 ltac:(fmP) ltac:(fmB)), A9. exact G10.
- rewrite (fm_kl _ _ _ 18 18%bv HPR8 ltac:(fmP) ltac:(fmB)), D18, (fm_kl _ _ _ 18 18%bv HPR6 ltac:(fmP) ltac:(fmB)), C18,
    (fm_kl _ _ _ 18 18%bv TK ltac:(fmP) ltac:(fmB)), B18, (fm_kl _ _ _ 18 18%bv PK2 ltac:(fmP) ltac:(fmB)), A18. exact G11.
- rewrite (fm_kl _ _ _ 19 19%bv HPR8 ltac:(fmP) ltac:(fmB)), D19, (fm_kl _ _ _ 19 19%bv HPR6 ltac:(fmP) ltac:(fmB)), C19,
    (fm_kl _ _ _ 19 19%bv TK ltac:(fmP) ltac:(fmB)). exact B19.
- rewrite (fm_kl _ _ _ 20 20%bv HPR8 ltac:(fmP) ltac:(fmB)), D20, (fm_kl _ _ _ 20 20%bv HPR6 ltac:(fmP) ltac:(fmB)), C20,
    (fm_kl _ _ _ 20 20%bv TK ltac:(fmP) ltac:(fmB)). exact B20.
- exact (fm_keep_trans _ _ _ KP7 (fm_keep_pres _ _ HPR8)).
- eapply fm_frame_kept; [exact AFR|]. intros a Ha. apply mbyte_of_aview. exact (FR a Ha).
- intros i Hi. apply aview_byte. rewrite MZ8 by lia. reflexivity.
- eapply fm_vm_fr; [|exact HHD0]. intros x Hx. apply mbyte_of_aview. apply HD. simpl Z.of_nat in Hx.
  change (as_ofl_head pcap_KS) with FM_HEAD in Hx. lia.
- exact HENV0.
- exact Hblk.
- exact HC.
- exact Hbok.
- exact Hn26.
Qed.

End W.

About rfmemopen_contract_pcap.
Print Assumptions rfmemopen_contract_pcap.

(* ---------------------------------------------------------------------------------------------- *)
(* 6. AINTR discharged: the core already proves the memset interceptor (A/AE32.v:568                 *)
(*    memset_icpt_realizes, the core's relocation). Its premises are exactly aintrin_realizes         *)
(*    OSet's body (Reusable/YG0d.v:318-335), up to the position of amem_range and the trivial         *)
(*    `OSet => True` premise; its post is aintrin_realizes's with the `match op` reduced at OSet.     *)
(*    The donor keeps AMEMSET as a Section hypothesis (cgif AC8l / AC8q / AC8s / AC8u) and discharges  *)
(*    it at instantiation; this is that instantiation for pcap. Needs commit 595c3188fe3 or later     *)
(*    (at e8bb946b7e4, AE32's import AE79 lacked its PcapImgEnd Require).                             *)
(* ---------------------------------------------------------------------------------------------- *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require AE32.

Lemma fm_aintr {fx : YK11.FPState} {rc : YM05.RunCeil} : forall B,
  AR_laws tfibsegs B -> PcapSyms B -> aintrin_realizes tfibsegs B OSet FM_MEMSET.
Proof.
intros B HL HT ly S W regs mem md d x n HE H10 H11 H12 Hn Hd Hdn Hdo Ham Hra Hsh _.
exact (AE32.memset_icpt_realizes B HL HT ly S W regs mem md d x n HE H10 H11 H12 Hn Hd Hdn Hdo Hra Hsh Ham).
Qed.

(* The contract with NO memset hypothesis: only the read stream's image laws and the core's symbol
   record remain, both discharged once at instantiation (rows 4 + 6). *)
Theorem rfmemopen_contract_pcap_noaintr {fx : YK11.FPState} {rc : YM05.RunCeil} :
  forall (SK : YI16.sink_head) (B : asyms) (MT : ameter_ops) (CTX : list (list Z)),
  asource_img_laws SK tfibsegs B pcap_KS -> PcapSyms B ->
  @rfmemopen_contract fx rc SK tfibsegs B pcap_KS MT CTX PFMEMOPEN FM_MALLOC_RA FM_MC_LO FM_MC_HI.
Proof.
intros SK B MT CTX HA HT.
exact (rfmemopen_contract_pcap SK B MT CTX HA HT (fm_aintr B (YG0q.AR_laws_ok tfibsegs B) HT)).
Qed.

About rfmemopen_contract_pcap_noaintr.
Print Assumptions rfmemopen_contract_pcap_noaintr.
