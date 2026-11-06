(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_link/lib/A/Rt/LinkFoMusl.v, with its module paths changed. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the walk of musl fmemopen on link's call
   fmemopen(g_said, 4096, "w") -- the proof of lib/A/Rt/LinkFoSpec.v's afmemopen_w_spec at the musl entry
   LA_FMEMOPEN 0x96a1c, with ra = LA_FM_MALLOC_RA 0x96ab8 and __strchrnul's window [0x10360, 0x10380).

   proves function fmemopen (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index fmemopen`)
   proves function __ofl_add (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __ofl_add`)
   proves function __ofl_lock (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __ofl_lock`)
   proves function __ofl_unlock (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __ofl_unlock`)
   proves function __lock (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __lock`)
   proves function __unlock (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __unlock`)

   PORTED from libreac/fuzz_pcap's released walk lib/A/Stdio/PFmemopenMW.v (origin/ossv/recipes), through its
   copy relocated to link's addresses (internal path (internal record, sha256 ae5097763714)):
   the six symbolic runs, the three callee contracts, the journal and the helpers are the donor's;
   the mode arm, the strchr results, the image facts and the post are link's.

   THE WALK (neutral listings in link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST)
   of fmemopen, __ofl_add, __ofl_lock, __ofl_unlock, __lock, __unlock), six symbolic runs and three callee contracts:
     A  0x96a1c .. jal strchr 0x96a4c            frame of 48, ra s0..s4 saved; strchr(mode, '+')
        afm_strchr_lit (STR) at 0x43054          -> 0
     B  0x96a50 .. jal strchr 0x96a60            mode[0] = 'w' (119) read; strchr("rwa", 'w')
        afm_strchr_lit                           -> "rwa" + 1 (0x20292)
     C  0x96a64 .. jal malloc 0x96ab4            beqz a0 not taken (0x20292 <> 0); bnez s1 TAKEN (s1 = g_said
                                                 0x62fee0 >= 4096)
        amalloc04_rule_d (AMR, LinkMallocDepot.v) through fm_malloc_d (PaJournalFs.amalloc04_sub_fs's lift, with
        the depot step); the call records a fixed row of the universe, so the depot's wild part does not grow
     D  0x96ab8 .. jal memset 0x96ad8            bnez a0 TAKEN: the malloc NULL branch 0x96abc is refuted
                                                 by amalloc04_rule's 4096 <= res (YC5d.v)
        aintrin_realizes OSet at 0x52d70 (AINTR) through YC85G.aj_intrin_atS
     E  0x96adc .. 0x971f4                       the FILE set-up stores (AMemFile.v amf_fm): +0x10c bnez s4
                                                 not taken (no '+'), +0x118 mode[0] <> 'r' so +0x11c / +0x128
                                                 flags = 4 (F_NORD); +0x134 / +0x13c neither 'a' nor 'r', so
                                                 +0x160 beqz s4 TAKEN (no c.len store, no strnlen, no store
                                                 into g_said); the epilogue, the tail jump into __ofl_add,
                                                 __ofl_lock / __lock (need_locks = 0) and f->next = old head (0)
     F  0x971f4 .. ret 0x9720c                   the head store (the only image byte written), __ofl_unlock
                                                 / __unlock (lock word 0), __ofl_add's epilogue and ret
   Runs A-D carry the journal through YCbq.SRr_run_AJ and run E through SRr_run_to_AJ (stack + the fresh
   FILE block). Run F writes the open-file list head, which awr_byte has no case for, so it is run plainly
   (YA0o.SRr_run_gen) and the journal is rebuilt by fm_head_journal, for the head alone (the footprint holds the
   sink token, so the journal spares the head: YCbq.v fp_spares).

   THE FOUR UNTAKEN ZERO RETURNS: 0x96a64 (strchr NULL) is excluded by STR's result for "rwa" (0x20292);
   0x96a68/0x96a6c (buf NULL, size sign) by s1 = g_said >= 4096; 0x96abc (malloc NULL) by 4096 <= res. No path of
   the walk reaches a report or CheckFailed entry: every function stepped here is uninstrumented musl, and the
   three wrapper calls are taken as contracts.

   THE IMAGE FACTS. The mode byte 0x21260, the stdio words (__libc.threaded 0x651ea1, __libc.need_locks 0x651ea3,
   ofl_lock 0x652300) and the head 0x652308 are image bytes outside as_owned_static and errno (fm_imgb, from TB:
   ts_owned = Tfib_owned_static, ts_errno = TFIB_ERRNO, AF0m.v), so the journal keeps the first four
   (fp_spares_off) and run F's head store is the one image write. The strchr calls' three memory premises (the
   mode word, "rwa\0", __strchrnul's constants) are image bytes below 0x30000; both calls happen before malloc and
   every step before them changes only the stack below the entry sp (fm_cells).

   SECTION HYPOTHESES (named; the file declares nothing else and leaves no proof open):
     TB     PcapSyms B (AF0m.v)                          -- link's symbol record
     AMR    amalloc04_rule_d tfibsegs B MT               -- the allocator rule of the malloc call +0x98, with the depot
                                                           step (LinkMallocDepot.v)
     AINTR  aintrin_realizes tfibsegs B OSet 0x52d70     -- the memset wrapper (AE32.v memset_icpt_realizes)
     STR    afm_strchr_lit B (LinkFoStrchrDef.v)          -- the two strchr calls at the wrapper's jump 0x43054 *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q YG0s YG0v YG0p YP08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AF0m AF0x AE2y AE39.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require YC85G YC4b PaJournalFs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AMemFileT06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec LinkFoStrchrDef LinkMallocDepot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* Frame files in the import closure (e.g. lib/A/AB14.v) set this flag to false globally; restore lia's div / mod
   handling in this file. The redefinition is LOCAL to this file: it does not escape the Require, so a file that
   Requires this one keeps its own setting. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. Addresses, read off the neutral listings of image A.                                          *)
(* ---------------------------------------------------------------------------------------------- *)
Definition FM_STRCHR : Z := 0x43054.   (* __interceptor_trampoline_strchr, target of 0x96a4c / 0x96a60 *)
Definition FM_RA1    : Z := 0x96a50.   (* after the first strchr call *)
Definition FM_RA2    : Z := 0x96a64.   (* after the second strchr call *)
Definition FM_MALLOC : Z := 0x540cc.   (* __interceptor_trampoline_malloc, target of 0x96ab4 *)
Definition FM_MEMSET : Z := 0x52d70.   (* __interceptor_trampoline_memset, target of 0x96ad8 *)
Definition FM_RA4    : Z := 0x96adc.   (* after the memset call *)
Definition FM_HEADST : Z := 0x971f4.   (* __ofl_add's `sd s0,0(a0)`, the head store *)
Definition FM_MODE   : Z := LA_MODE_W. (* "w\0", the mode string mark_quietly passes *)
Definition FM_RWA    : Z := 0x20291.   (* "rwa\0" = LA_RWA *)
Definition FM_THR    : Z := 0x651ea1.  (* __libc+1 = amf_threaded link_amf *)
Definition FM_NL     : Z := 0x651ea3.  (* __libc+3 = amf_need_locks link_amf *)
Definition FM_LOCK   : Z := 0x652300.  (* ofl_lock = amf_ofl_lock link_amf *)
Definition FM_HEAD   : Z := 0x652308.  (* ofl_head = amf_ofl_head link_amf *)
Local Abbreviation FPT := afmemopen_w_fp.

(* ---------------------------------------------------------------------------------------------- *)
(* 2. The code table: fmemopen (116 words) and the musl functions the tail reaches.                *)
(* ---------------------------------------------------------------------------------------------- *)
Definition fm_ranges : list (Z * nat) :=
  [ (LA_FMEMOPEN, 116%nat); (0x97194, 12%nat); (0x971c4, 3%nat); (0x971d0, 16%nat);
    (0x9b4d4, 162%nat); (0x9b75c, 29%nat) ].
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
  clookup fm_tbl LA_FMEMOPEN = Some 0xfd010113 /\ clookup fm_tbl 0x9720c = Some 0x00008067 /\
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

(* A: the entry; a2 = the "w" literal. *)
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition ssA : sstate := mkSS LA_FMEMOPEN (sr_set sr_atoms 12%bv (SLit FM_MODE)) [stkA] None
  (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition eA : sstate := Eval vm_compute in fst (fm_RUN ssA).
Lemma r_A : fm_RUN ssA = (eA, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* B: strchr(mode, '+') returned 0; s3 = the "w" literal, whose first byte is 'w' (119). *)
Definition modeR : YP09.region := YP09.mkRegion None FM_MODE (FM_MODE + 1) 0 0 [ck FM_MODE 1 (SLit 119)].
Definition ssB : sstate := mkSS FM_RA1 (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 19%bv (SLit FM_MODE)) [modeR] None
  (mkFacts [] [] []).
Definition eB : sstate := Eval vm_compute in fst (fm_RUN ssB).
Lemma r_B : fm_RUN ssB = (eB, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* C: strchr("rwa", 'w') returned "rwa" + 1; s1 = g_said >= 4096. *)
Definition ssC : sstate := mkSS FM_RA2 (sr_set sr_atoms 10%bv (SLit (FM_RWA + 1))) [] None
  (mkFacts [(9%nat, mkAF 4096 (2^47) 0)] [] []).
Definition eC : sstate := Eval vm_compute in fst (fm_RUN ssC).
Lemma r_C : fm_RUN ssC = (eC, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

(* D: malloc returned res >= 4096, 16-aligned. *)
Definition ssD : sstate := mkSS LA_FM_MALLOC_RA sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2^47) 4)] [] []).
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
(* 4. Generic helpers over tfibsegs.                                                                *)
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
(* a zero chunk of region i covering [o, o + len) *)
Definition zcov_at (ss : sstate) (i : nat) (o len : Z) : bool :=
  match nth_error (ss_mem ss) i with
  | Some r => existsb (fun c =>
                match YP09.c_val c with
                | CZero l => (YP09.c_off c <=? o) && (o + len <=? YP09.c_off c + l)
                | _ => false
                end) (YP09.r_chunks r)
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

Lemma fm_zcov_val : forall E ss (H : word -> bool) ms i bn o (n : nat),
  st_ok tfibsegs E ss (restrict H ms) -> zcov_at ss i o (Z.of_nat n) = true -> rbase_at ss i = Some bn ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E bn) + o) n 0.
Proof.
intros E ss H ms i bn o n HS Hc Hb.
unfold zcov_at in Hc. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
apply existsb_exists in Hc as ([off cv] & Hin & Hck). cbn [YP09.c_off YP09.c_val] in Hck.
destruct cv as [n' e|l0|l0|d0 s0 l0]; try discriminate.
apply andb_prop in Hck as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply (fm_zchunk_val E ss H ms i off l0 bn o n HS); [| exact Hb | exact H1 | exact H2].
unfold zchunk_at. rewrite Hi. apply existsb_exists. exists (YP09.mkChunk off (CZero l0)). split; [exact Hin|].
cbn [YP09.c_off YP09.c_val]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma fm_vm_fr : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

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

(* The first byte of the mode word is mode[0] = 'w'. *)
Lemma fm_mode1 : forall m, val_mem tfibsegs m FM_MODE 8 119 -> val_mem tfibsegs m FM_MODE 1 119.
Proof. intros m H k Hk. assert (k = 0%nat) as -> by lia. rewrite (H 0%nat ltac:(lia)). reflexivity. Qed.

End H.

Definition fm_keep (r0 r1 : bvmap 5 word) : Prop :=
  forall r, In r [3; 4; 21; 22; 23; 24; 25; 26; 27] -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Lemma fm_keep_trans : forall r0 r1 r2, fm_keep r0 r1 -> fm_keep r1 r2 -> fm_keep r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma fm_keep_pres : forall r0 r1, aregs_preserved r0 r1 -> fm_keep r0 r1.
Proof. intros r0 r1 H r Hr. apply H. unfold acallee_saved. cbn [In] in Hr. lia. Qed.
Lemma fm_keep_kepts : forall r0 r1,
  (forall r, In r FSC_KEPT -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) -> fm_keep r0 r1.
Proof. intros r0 r1 H r Hr. apply H. unfold FSC_KEPT. cbn [In] in Hr |- *. tauto. Qed.

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

(* The FILE fields the "w" arm leaves (AMemFileSink.v amemfile_static, flags F_NORD, orientation 0, the window
   empty, cookie pos and len 0), with bw / nw the values of s1 (buf) and s2 (size). *)
Definition fm_wfile (m : word -> option byte) (f : Z) (bw nw : word) : Prop :=
  val_mem tfibsegs m (f + 0) 4 AF_NORD /\ val_mem tfibsegs m (f + 8) 8 0 /\ val_mem tfibsegs m (f + 16) 8 0 /\
  val_mem tfibsegs m (f + 24) 8 (amf_close link_amf) /\
  val_mem tfibsegs m (f + 32) 8 0 /\ val_mem tfibsegs m (f + 40) 8 0 /\ val_mem tfibsegs m (f + 48) 8 0 /\
  val_mem tfibsegs m (f + 56) 8 0 /\
  val_mem tfibsegs m (f + 64) 8 (amf_read link_amf) /\ val_mem tfibsegs m (f + 72) 8 (amf_write link_amf) /\
  val_mem tfibsegs m (f + 80) 8 (amf_seek link_amf) /\ val_mem tfibsegs m (f + 88) 8 (f + AMF_BUF) /\
  val_mem tfibsegs m (f + 96) 8 AMF_BUFSIZ /\ val_mem tfibsegs m (f + 104) 8 0 /\ val_mem tfibsegs m (f + 112) 8 0 /\
  val_mem tfibsegs m (f + 120) 4 AU32M1 /\ val_mem tfibsegs m (f + 124) 4 0 /\ val_mem tfibsegs m (f + 128) 8 0 /\
  val_mem tfibsegs m (f + 136) 4 0 /\
  val_mem tfibsegs m (f + 140) 4 AU32M1 /\ val_mem tfibsegs m (f + 144) 4 AU32M1 /\
  val_mem tfibsegs m (f + 152) 8 (f + AMF_COOKIE) /\
  val_mem tfibsegs m (f + 160) 8 0 /\ val_mem tfibsegs m (f + 168) 8 0 /\ val_mem tfibsegs m (f + 176) 8 0 /\
  val_mem tfibsegs m (f + 184) 8 0 /\ val_mem tfibsegs m (f + 192) 8 0 /\ val_mem tfibsegs m (f + 200) 8 0 /\
  val_mem tfibsegs m (f + 208) 8 0 /\ val_mem tfibsegs m (f + 216) 8 0 /\ val_mem tfibsegs m (f + 224) 8 0 /\
  val_mem tfibsegs m (f + 232) 8 0 /\ val_mem tfibsegs m (f + 240) 8 0 /\
  val_mem tfibsegs m (f + 248) 8 (bv_unsigned nw) /\ val_mem tfibsegs m (f + 256) 8 (bv_unsigned bw) /\
  val_mem tfibsegs m (f + 264) 4 (amf_mode link_amf).

Lemma fm_wfile_kept : forall m m' f bw nw, fm_wfile m f bw nw ->
  (forall a, f <= a < f + 272 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> fm_wfile m' f bw nw.
Proof.
intros m m' f bw nw H Hk. unfold fm_wfile in *.
repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  end.
repeat split; (eapply fm_vm_fr; [|eassumption]); intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia.
Qed.

Lemma fm_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

(* link's FILE from the fields: amemfile_at with the window empty, and the seven words at their open values. *)
Ltac fmS := cbn [amf_buf amf_size amf_mode amf_read amf_write amf_seek amf_close link_amf]; lia.
Lemma fm_amf : forall m f, 0 < f -> f + AMF_BLOCK <= 2 ^ 64 -> f mod 16 = 0 ->
  fm_wfile m f (w64 (amf_buf link_amf)) (w64 (amf_size link_amf)) ->
  amf_k tfibsegs link_amf m f 0 /\ amf_dyn tfibsegs link_amf m f AF_NORD 0 0 0 0 0 0.
Proof.
intros m f H0 H1 H2 HF.
pose proof HF as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 &
  V120 & V124 & V128 & V136 & V140 & V144 & V152 & V160 & V168 & V176 & V184 & V192 & V200 & V208 & V216 & V224 &
  V232 & V240 & V248 & V256 & V264).
rewrite fm_w64u in V248 by fmS. rewrite fm_w64u in V256 by fmS.
assert (Hsz : 0 <= amf_size link_amf) by fmS.
split.
- split.
  + split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
    split.
    { unfold amemfile_static.
      split; [exact V24|]. split; [exact V48|]. split; [exact V64|]. split; [exact V72|]. split; [exact V80|].
      split; [exact V88|]. split; [exact V96|]. split; [exact V104|]. split; [exact V112|].
      split; [exact V120|]. split; [exact V124|]. split; [exact V128|]. split; [exact V140|]. split; [exact V144|].
      split; [exact V152|]. split; [exact V160|]. split; [exact V168|]. split; [exact V176|]. split; [exact V184|].
      split; [exact V192|]. split; [exact V200|]. split; [exact V208|]. split; [exact V216|]. split; [exact V224|].
      split; [exact V248|]. split; [exact V256 | exact V264]. }
    split; [left; exact V0|].
    split; [left; exact V136|].
    split.
    { split; [exact V8|]. split; [exact V16|]. left. split; [exact V32|]. split; [exact V40 | exact V56]. }
    exists 0, 0. split; [lia|]. split; [exact Hsz|]. split; [exact V232 | exact V240].
  + left. split; [reflexivity|]. split; [exact V32|]. split; [exact V40 | exact V56].
- unfold amf_dyn.
  split; [unfold AF_NORD; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hsz|]. split; [exact V0|]. split; [exact V136|]. split; [exact V32|]. split; [exact V40|].
  split; [exact V56|]. split; [exact V232 | exact V240].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 5. The walk, over link's ASan image tfibsegs = Asan.M.loaded_segments.                          *)
(* ---------------------------------------------------------------------------------------------- *)
Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.
Local Abbreviation AJ := (@ajournal rc link_asink_head tfibsegs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation STK := AFMW_STK.

(* NAMED SECTION HYPOTHESES. *)
(* link's symbol record (lib/A/AF0m.v). *)
Hypothesis TB : PcapSyms B.
(* The allocator rule for the malloc call +0x98, with the depot step of its trace (lib/A/Rt/LinkMallocDepot.v). *)
Hypothesis AMR : amalloc04_rule_d (SK := link_asink_head) tfibsegs B MT.
(* The ASan memset wrapper at its trampoline 0x52d70 = FM_MEMSET (lib/A/AE32.v memset_icpt_realizes states it). *)
Hypothesis AINTR : aintrin_realizes tfibsegs B OSet 0x52d70.
(* The two strchr calls at the strchr wrapper's jump 0x43054 (lib/A/Rt/LinkFoStrchrDef.v). *)
Hypothesis STR : afm_strchr_lit B.

(* 5.1 The image bytes the walk reads past the entry: image bytes outside the allocator's statics and errno
   (from TB, AF0m.v), so the journal keeps them unless they are the head. *)
Definition fm_imgok (a : Z) : Prop :=
  in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition fm_nown (a : Z) : bool :=
  forallb (fun r => negb ((fst r <=? a) && (a <? fst r + snd r))) Tfib_owned_static.
Definition fm_imgb (a : Z) : bool :=
  AMemFileT06.in_imgb tfibsegs a && fm_nown a && negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4)).

Lemma fm_imgb_ok : forall a, fm_imgb a = true -> fm_imgok a.
Proof.
intros a H. unfold fm_imgb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
unfold fm_imgok. rewrite (ts_owned B TB), (ts_errno B TB).
split; [exact (AMemFileT06.in_imgb_sound _ _ H1)|]. split.
- intros HX. apply Exists_exists in HX as (r & Hin & Hr). unfold fm_nown in H2. rewrite forallb_forall in H2.
  specialize (H2 r Hin). unfold in_zr in Hr. apply negb_true_iff, andb_false_iff in H2.
  destruct H2 as [H2|H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
- apply negb_true_iff, andb_false_iff in H3.
  destruct H3 as [H3|H3]; [apply Z.leb_gt in H3 | apply Z.ltb_ge in H3]; lia.
Qed.

Lemma fm_imgb_range : forall lo n, forallb (fun k => fm_imgb (lo + Z.of_nat k)) (seq 0 n) = true ->
  forall a, lo <= a < lo + Z.of_nat n -> fm_imgok a.
Proof.
intros lo n H a Ha. rewrite forallb_forall in H. specialize (H (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia. exact (fm_imgb_ok a H).
Qed.

Lemma fm_head_img : forall a, FM_HEAD <= a < FM_HEAD + 8 -> fm_imgok a.
Proof. intros a Ha. apply (fm_imgb_range FM_HEAD 8); [vm_compute; reflexivity | simpl Z.of_nat; lia]. Qed.

Lemma fm_env_img : forall a, amf_env_addr link_amf a -> fm_imgok a.
Proof.
intros a Ha. cbv [amf_env_addr amf_threaded amf_need_locks amf_ofl_lock link_amf] in Ha.
destruct Ha as [-> | [-> | Ha]].
- apply fm_imgb_ok. vm_compute. reflexivity.
- apply fm_imgb_ok. vm_compute. reflexivity.
- apply (fm_imgb_range 0x652300 4); [vm_compute; reflexivity | simpl Z.of_nat; lia].
Qed.

Lemma fm_mode_img : fm_imgok FM_MODE.
Proof. apply fm_imgb_ok. vm_compute. reflexivity. Qed.

(* 5.2 The strchr calls' three memory premises (the mode word, "rwa\0", __strchrnul's constants), carried from
   the entry: image bytes in [0x10000, 0x30000), which no step before malloc writes. *)
Definition fm_sargs (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  val_mem tfibsegs (rd W mem) LA_MODE_W 8 119 /\ garr8 tfibsegs (rd W mem) LA_RWA rwa_Z /\ mconsts_view W mem.

Lemma fm_cells : forall (W : world tfibsegs) mem mem', fm_sargs W mem ->
  (forall a, 0x10000 <= a < 0x30000 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  fm_sargs W mem'.
Proof.
intros W mem mem' (V & G & M) K. pose proof mc_bounds as [MB1 MB2].
split; [|split].
- eapply fm_vm_fr; [|exact V]. intros x Hx. apply mbyte_of_aview. apply K.
  simpl Z.of_nat in Hx. unfold LA_MODE_W in Hx. lia.
- eapply garr8_frame; [exact G|]. intros x Hx. apply mbyte_of_aview. apply K.
  unfold rwa_Z in Hx. cbn [length] in Hx. simpl Z.of_nat in Hx. unfold LA_RWA in Hx. lia.
- apply (mconsts_view_keep W mem mem' M). intros a Ha. apply K. rewrite MB1, MB2 in Ha. lia.
Qed.

(* 5.3 One strchr call, composed with the journal (both calls happen before malloc: lyc Sc = ly S). *)
Lemma fm_strchr_step : forall s c res (W W0 : world tfibsegs) ly S mem0 md0 regs mem md sp0
    (Q : world tfibsegs -> config -> Prop),
  In (s, c, res) FSC_INST ->
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 ->
  spZ regs = sp0 - 48 -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  fm_sargs W mem ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 10 = w64 res -> getr regs1 1 = getr regs 1 -> getr regs1 2 = getr regs 2 ->
     (forall r, In r FSC_KEPT -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 - FSC_WIN <= a < sp0 - 48) ->
        aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W (cfg_at tfibsegs (raZ regs) regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs FM_STRCHR regs mem md) Q.
Proof.
intros s c res W W0 ly S mem0 md0 regs mem md sp0 Q Hin HJ Hsp Hra G10 G11 (HMW & HRW & HMC) K.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
eapply SRr_bind.
{ apply (STR s c res Hin ly S W regs mem md HAR Hra); try assumption.
  - rewrite Hsp. rewrite Zminus_mod, Hal16. reflexivity.
  - unfold FSC_WIN. rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - intros a Ha. apply Hpres. rewrite Hsp in Ha. unfold FSC_WIN in Ha. lia. }
cbv beta. intros W' c' _ (-> & regs1 & mem1 & md1 & -> & SBM & HAR1 & H10 & H1 & H2 & HK & AV & PRS & PM).
rewrite Hsp in AV, PRS.
apply K; [| exact SBM | exact H10 | exact H1 | exact H2 | exact HK | exact AV].
eapply (ajournal_after_write tfibsegs B LAWS fm_segs_low STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem md 0 mem1 md1
  (fun a => sp0 - 48 - FSC_WIN <= a < sp0 - 48) S [] HJ).
- intros a Ha Hna. exact (AV a Ha Hna).
- exact PM.
- exact SBM.
- intros a Ha. left. left. rewrite FS. unfold FSC_WIN in Ha. lia.
- exact HAR1.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

(* 5.4 The journal across a write confined to musl's open-file-list head (8 bytes at 0x652308): the donor's
   form (pcap's Theorem Labs lane wf_frameW / wf_journal_write) for the head alone. awr_byte (YCbq.v) has no case for
   the head; the journal keeps it free because the footprint holds the sink token (fp_spares). *)
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
assert (HHD : @AOFL_HEAD link_asink_head = FM_HEAD) by reflexivity.
assert (HIMG : forall a, FM_HEAD <= a < FM_HEAD + 8 ->
  in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
  by exact fm_head_img.
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

(* 5.5 The stdio words and the mode byte survive any journal: image bytes outside the statics, errno and the head. *)
Lemma fm_img_kept : forall STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k a,
  AJ STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k -> fm_imgok a -> ~ (FM_HEAD <= a < FM_HEAD + 8) ->
  mbyte tfibsegs (rd W' mem') a = mbyte tfibsegs (rd W mem) a.
Proof.
intros STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k a HJ (Hi & Hns & He) Hh.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply mbyte_of_aview. apply (F3 a Hi Hns He). apply fp_spares_off. exact Hh.
Qed.

Lemma fm_env_kept : forall STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  AJ STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  amf_env tfibsegs link_amf (rd W mem) -> amf_env tfibsegs link_amf (rd W' mem').
Proof.
intros STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HE.
apply (amf_env_frame tfibsegs link_amf (rd W mem) (rd W' mem')); [|exact HE].
intros a Ha. apply (fm_img_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (fm_env_img a Ha)).
cbv [amf_env_addr amf_threaded amf_need_locks amf_ofl_lock link_amf] in Ha. unfold FM_HEAD. lia.
Qed.

Lemma fm_mode_kept : forall STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  AJ STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  val_mem tfibsegs (rd W mem) FM_MODE 1 119 -> val_mem tfibsegs (rd W' mem') FM_MODE 1 119.
Proof.
intros STK0 sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HV.
eapply fm_vm_fr; [|exact HV]. intros x Hx. simpl Z.of_nat in Hx. assert (x = FM_MODE) as -> by lia.
apply (fm_img_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FM_MODE HJ fm_mode_img). unfold FM_MODE, LA_MODE_W, FM_HEAD. lia.
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
  SRr tfibsegs W (cfg_at tfibsegs LA_FMEMOPEN regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 regs mem md Q HJ G12 K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo, Hpres.
set (sp0 := spZ regs) in *.
remember (Ereg regs []) as E eqn:HE.
assert (E2u : bv_unsigned (ew E 2) = sp0) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 LA_FMEMOPEN) with (Z_to_bv 64 (ss_pc ssA)).
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
  val_mem tfibsegs (rd W mem) FM_MODE 1 119 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 FM_RA2 -> getr regs1 10 = w64 FM_RWA -> getr regs1 11 = w64 119 ->
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
    split; [unfold FM_MODE, LA_MODE_W; lia|]. split; [unfold FM_MODE, LA_MODE_W; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. unfold ck.
    apply (chunk_ok_val tfibsegs E _ 0 FM_MODE 1%N (SLit 119) 119); [reflexivity | cbn; lia | cbn; lia | exact VM].
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
- fm_lit E eB HS1 119.
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
  getr regs 10 = w64 (FM_RWA + 1) -> 4096 <= bv_unsigned (getr regs 9) <= 2 ^ 47 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly S W mem1 md1 0 ->
     same_but_materialized md md1 ->
     getr regs1 1 = w64 LA_FM_MALLOC_RA -> getr regs1 10 = w64 AMF_BLOCK ->
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
- fm_lit E eC HS1 LA_FM_MALLOC_RA.
- fm_lit E eC HS1 AMF_BLOCK.
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

(* 5.9 Phase D: from malloc's return (res >= 4096, so `bnez a0` at 0x96ab8 is taken) to the memset call. *)
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
  SRr tfibsegs W (cfg_at tfibsegs LA_FM_MALLOC_RA regs mem md) Q.
Proof.
intros W W0 ly S mem0 md0 lyc Sc sp0 regs mem md k Q HJ Hb10 Hal10 K.
remember (Ereg regs []) as E eqn:HE.
assert (E10u : bv_unsigned (ew E 10) = bv_unsigned (getr regs 10)) by (rewrite HE, (ew_Ereg_nat regs _ 10 10%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 LA_FM_MALLOC_RA) with (Z_to_bv 64 (ss_pc ssD)).
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

(* 5.10 Phase E: from memset's return through the FILE set-up ("w": flags F_NORD, no c.len), the epilogue, the
   tail jump into __ofl_add, __ofl_lock / __lock (need_locks = 0) and f->next = old head (0), up to the head
   store 0x971f4. *)
Lemma fm_E : forall (W W0 : world tfibsegs) ly S mem0 md0 ly2 S2 sp0 regs regs0 mem md res
    (Q : world tfibsegs -> config -> Prop),
  AJ STK sp0 FPT ly S W0 mem0 md0 [] ly2 S2 W mem md 1 ->
  In (res, AMF_BLOCK) (ablocks B ly2 S2) -> ~ In (res, AMF_BLOCK) (ablocks B ly S) ->
  spZ regs = sp0 - 48 -> getr regs 8 = w64 res ->
  4096 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> getr regs 19 = w64 FM_MODE -> getr regs 20 = w64 0 ->
  fm_frame sp0 (rd W mem) regs0 ->
  (forall i, 0 <= i < 272 -> mbyte tfibsegs (rd W mem) (res + i) = Some (Z_to_bv 8 0)) ->
  val_mem tfibsegs (rd W mem) FM_MODE 1 119 -> val_mem tfibsegs (rd W mem) FM_THR 1 0 ->
  val_mem tfibsegs (rd W mem) FM_NL 1 0 -> val_mem tfibsegs (rd W mem) FM_HEAD 8 0 ->
  (forall regs1 mem1 md1,
     AJ STK sp0 FPT ly S W0 mem0 md0 [] ly2 S2 W mem1 md1 1 ->
     same_but_materialized md md1 ->
     getr regs1 10 = w64 FM_HEAD -> getr regs1 2 = w64 (sp0 - 16) -> getr regs1 8 = w64 res ->
     getr regs1 9 = getr regs0 9 -> getr regs1 18 = getr regs0 18 -> getr regs1 19 = getr regs0 19 ->
     getr regs1 20 = getr regs0 20 -> fm_keep regs regs1 ->
     val_mem tfibsegs (rd W mem1) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
     val_mem tfibsegs (rd W mem1) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
     fm_wfile (rd W mem1) res (getr regs 9) (getr regs 18) ->
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
destruct (al_blocks _ _ LAWS ly2 S2 W mem md res AMF_BLOCK HAR Hblk2) as (Hf16 & Hf4 & Hfceil & Hfapp & Hfb & _).
change (req_size AMF_BLOCK) with 1304 in Hfceil, Hfb.
assert (IMGX : forall a, (FM_MODE <= a < FM_MODE + 1) \/ a = FM_THR \/ a = FM_NL \/ (FM_HEAD <= a < FM_HEAD + 8) ->
  in_img tfibsegs a).
{ intros a [Ha | [-> | [-> | Ha]]].
  - assert (a = FM_MODE) as -> by lia. exact (proj1 fm_mode_img).
  - exact (proj1 (fm_env_img FM_THR ltac:(left; reflexivity))).
  - exact (proj1 (fm_env_img FM_NL ltac:(right; left; reflexivity))).
  - exact (proj1 (fm_head_img a Ha)). }
assert (DJ : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> in_img tfibsegs a) -> res + 1304 <= lo \/ hi <= res).
{ intros lo hi Hlh Hi. destruct (Z_le_gt_dec lo res) as [L|L].
  - destruct (Z_lt_ge_dec res hi) as [L2|L2]; [|right; lia]. exfalso.
    apply (blk_img tfibsegs B LAWS ly2 S2 W mem md res AMF_BLOCK res HAR Hblk2);
      [change (req_size AMF_BLOCK) with 1304; lia | apply Hi; lia].
  - destruct (Z_lt_ge_dec lo (res + 1304)) as [L2|L2]; [|left; lia]. exfalso.
    apply (blk_img tfibsegs B LAWS ly2 S2 W mem md res AMF_BLOCK lo HAR Hblk2);
      [change (req_size AMF_BLOCK) with 1304; lia | apply Hi; lia]. }
pose proof (DJ FM_MODE (FM_MODE + 1) ltac:(lia) (fun a Ha => IMGX a ltac:(lia))) as DJm.
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
      split; [unfold FM_MODE, LA_MODE_W; lia|]. split; [unfold FM_MODE, LA_MODE_W; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold ck.
      apply (chunk_ok_val tfibsegs E _ 0 FM_MODE 1%N (SLit 119) 119); [reflexivity | cbn; lia | cbn; lia | exact VMODE].
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
    unfold FM_MODE, LA_MODE_W, FM_THR, FM_NL, FM_HEAD in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2u, E8u, E9. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
eapply (SRr_run_to_AJ tfibsegs B LAWS fm_segs_low fm_tbl fm_tbl_ok fm_wx W FUEL FM_HEADST E ssE eE _ _ STK sp0 FPT
  ly S W0 mem0 md0 [] ly2 S2 md 1 Q HS r_E I HJ).
{ unfold ssE. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off E stkE _ STK sp0 FPT (ablocks B ly S) (ablocks B ly2 S2) ly2 [] 2 (-48));
    [reflexivity | rewrite E2u; lia | cbn [YP09.r_wlo stkE]; rewrite FS; lia | cbn [YP09.r_whi stkE]; lia |].
  eapply (awr_ok_cons_tmp E fileE _ STK sp0 FPT (ablocks B ly S) (ablocks B ly2 S2) ly2 [] 8 res AMF_BLOCK);
    [reflexivity | exact E8u | exact Hblk2 | exact Hnew | cbn; lia | cbn [YP09.r_whi fileE]; change (req_size AMF_BLOCK) with 1304; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
intros ms1 mat1 HS1 HJ1 HF1 HFr1 Hgr1. cbn [ms_mem mkst] in HJ1, HF1, HFr1, Hgr1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E eE ms1 HS1 eq_refl).
assert (CV : forall off (n : N) v, chunk_at eE 1 off n v = true -> Z.of_N n <= 8 ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (res + off) (N.to_nat n) (bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N n))).
{ intros off n v Hc Hn. pose proof (fm_chunk_val E eE (w_H W) ms1 1 off n v 8 HS1 Hc eq_refl Hn) as V.
  rewrite E8u in V. exact V. }
assert (CZ : forall o (n : nat), zcov_at eE 1 o (Z.of_nat n) = true ->
  val_mem tfibsegs (rd W (ms_mem ms1)) (res + o) n 0).
{ intros o n Hc. pose proof (fm_zcov_val E eE (w_H W) ms1 1 8 o n HS1 Hc eq_refl) as V.
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
- unfold fm_wfile.
  split; [exact (LV 0 4%N 4 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 8 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 16 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (LV 24 8%N (amf_close link_amf) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(fmS))|].
  split; [exact (CZ 32 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 40 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 48 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 56 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (LV 64 8%N (amf_read link_amf) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(fmS))|].
  split; [exact (LV 72 8%N (amf_write link_amf) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(fmS))|].
  split; [exact (LV 80 8%N (amf_seek link_amf) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(fmS))|].
  split; [pose proof (CV 88 8%N (SOff 8 280) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_off_val E 8 280 res E8u ltac:(lia)) in V; exact V|].
  split; [exact (LV 96 8%N 1024 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 104 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (LV 112 8%N 0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 120 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (CZ 124 4%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 128 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 136 4%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (LV 140 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [exact (LV 144 4%N 18446744073709551615 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
  split; [pose proof (CV 152 8%N (SOff 8 232) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_off_val E 8 232 res E8u ltac:(lia)) in V; exact V|].
  split; [exact (CZ 160 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 168 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 176 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 184 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 192 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 200 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 208 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 216 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 224 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 232 8%nat ltac:(vm_compute; reflexivity))|].
  split; [exact (CZ 240 8%nat ltac:(vm_compute; reflexivity))|].
  split; [pose proof (CV 248 8%N (SOff 18 0) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_soff0 E 18 (getr regs 18) E18) in V; exact V|].
  split; [pose proof (CV 256 8%N (SOff 9 0) ltac:(vm_compute; reflexivity) ltac:(lia)) as V;
          rewrite (fm_soff0 E 9 (getr regs 9) E9) in V; exact V|].
  exact (LV 264 4%N (amf_mode link_amf) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(fmS)).
- intros a Ha H1 H2. apply (fm_mb_frame E (ss_mem ssE) _ _ a HFr1 Ha). unfold ssE. cbn [ss_mem]. apply fm_nwr_all.
  repeat (apply Forall_cons; [unfold stkE, fileE, modeR, thrR, nlR, headR; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    rewrite ?E2u, ?E8u; lia|]). apply Forall_nil.
Qed.

(* 5.11 musl's open-file-list head is a writable image cell (.bss), measured on the image (the donor's form, after
   pcap's Theorem Labs lane wf_ofl_img_facts / wf_ofl_writable). *)
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

(* 5.12 Phase F: the head store `sd s0,0(a0)` (head = f), __ofl_unlock / __unlock (lock word 0), __ofl_add's
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

(* 5.13 Small transport helpers. *)
Lemma fm_sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof.
intros m m' H. pose proof (same_but_materialized_frame m m' H) as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & F2 & _).
exact (conj F1 F2).
Qed.
Lemma fm_w64_un : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma fm_av_mb : forall (W W' : world tfibsegs) m m' a,
  mbyte tfibsegs (rd W' m') a = mbyte tfibsegs (rd W m) a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a.
Proof. intros W W' m m' a H. unfold aview. rewrite H. reflexivity. Qed.
Lemma fm_kl : forall (P : Z -> Prop) (r0 r1 : bvmap 5 word) r (rb : bv 5),
  (forall r, P r -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) -> P r -> Z_to_bv 5 r = rb -> getr r1 rb = getr r0 rb.
Proof. intros P r0 r1 r rb H Hp <-. exact (H r Hp). Qed.
Ltac fmP := first [unfold acallee_saved; lia | unfold FSC_KEPT; cbn [In]; tauto | cbn [In]; tauto].
Ltac fmB := apply bv_eq; reflexivity.

Lemma fm_fresh : forall ly S ly2 S2 (W : world tfibsegs) mem md res,
  AR tfibsegs B ly2 S2 W mem md -> ablocks B ly2 S2 = ablocks B ly S ++ [(res, AMF_BLOCK)] ->
  ~ In (res, AMF_BLOCK) (ablocks B ly S).
Proof.
intros ly S ly2 S2 W mem md res HAR Hab Hin.
assert (Hb : In (res, AMF_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W mem md res AMF_BLOCK HAR Hb) as (_ & _ & _ & _ & _ & Hdisj & _).
rewrite Hab, map_app in Hdisj. cbn [map fst snd] in Hdisj.
pose proof (YG0s.pairwise_In _ _ (res, req_size AMF_BLOCK) (res, req_size AMF_BLOCK) _ _ eq_refl Hdisj
  ltac:(apply in_map_iff; exists (res, AMF_BLOCK); split; [reflexivity | exact Hin]) ltac:(left; reflexivity)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. change (req_size AMF_BLOCK) with 1304 in HD. lia.
Qed.

(* 5.14 The malloc call through AMR: YC85G.amalloc04_sub and PaJournalFs.amalloc04_sub_fs for amalloc04_rule_d
   (the callee's fresh journal with footprint [] composed into the walk's; the descriptors and the file system kept,
   since [] is sink-closed), with the rule's depot step carried to the caller. *)
Lemma fm_malloc_d : forall W regsT memT STK0 sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
  AJ STK0 sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_malloc MT n) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
     AJ STK0 sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
     4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
     acall_kept tfibsegs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
     mo_le MT Sc S2 (mo_malloc MT n) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
     YGwildCount.depot_step (call_trace lyc (pc_malloc_ra0 (as_code B)) regsT ch) (st_depot Sc) (st_depot S2)).
Proof.
intros W regsT memT STK0 sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp
  Hra Hraw Hnev Hch HU MOK.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
pose proof (ajournal_sub_init tfibsegs B STK0 sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ASTACK (sp0 + o) [] o
  HJ eq_refl Ho16 Ho ltac:(lia) Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AMR W regsT memT ASTACK (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 n 0 raw ch HJ1 Ha0 Hn Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact HU | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & MLE & DEP).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (YC85G.ajournal_sub_tok tfibsegs B LAWS fm_segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - ASTACK) with (sp0 + o - ASTACK) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact MLE|].
destruct (PaJournalFs.ajournal_closed_fs link_asink_head tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ2)
  as [Efd Efs].
split; [exact Efd|]. split; [exact Efs | exact DEP].
Qed.

(* 5.15 The tail: from memset's return to the contract's post. *)
Lemma fm_tail : forall (W W2 : world tfibsegs) ly S mem md ly2 S2 regs regsM memM mdM res,
  AJ STK (spZ regs) FPT ly S W mem md [] ly2 S2 W2 memM mdM 1 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, AMF_BLOCK)] ->
  mo_le MT S S2 (mo_malloc MT AMF_BLOCK) ->
  m_fds mdM = m_fds md -> m_fs mdM = m_fs md ->
  YK0s.ret_ok (getr regs 1) ->
  getr regsM 2 = w64 (spZ regs - 48) -> getr regsM 8 = w64 res -> getr regsM 9 = w64 (amf_buf link_amf) ->
  getr regsM 18 = w64 (amf_size link_amf) -> getr regsM 19 = w64 FM_MODE -> getr regsM 20 = w64 0 ->
  fm_keep regs regsM ->
  fm_frame (spZ regs) (rd W2 memM) regs ->
  (forall i, 0 <= i < 272 -> mbyte tfibsegs (rd W2 memM) (res + i) = Some (Z_to_bv 8 0)) ->
  val_mem tfibsegs (rd W2 memM) FM_HEAD 8 0 ->
  amf_env tfibsegs link_amf (rd W mem) -> val_mem tfibsegs (rd W mem) FM_MODE 1 119 ->
  (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot S)))%nat ->
  SRr tfibsegs W2 (cfg_at tfibsegs FM_RA4 regsM memM mdM)
    (afm_w_post (SK := link_asink_head) tfibsegs B link_amf MT regs ly S W mem md).
Proof.
intros W W2 ly S mem md ly2 S2 regs regsM memM mdM res JM Hab2 Hmo2 Fd Fs Hra M2 M8 M9 M18 M19 M20 MK MFR MZ MHD
  HENV0 VMODE0 HWILD.
set (sp0 := spZ regs) in *.
pose proof JM as (HARM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo.
assert (Hblk2 : In (res, AMF_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM res AMF_BLOCK HARM Hblk2) as (Hf16 & Hf4 & Hfceil & _ & _ & Hfdisj & _).
change (req_size AMF_BLOCK) with 1304 in Hfceil.
assert (Hnew : ~ In (res, AMF_BLOCK) (ablocks B ly S)) by exact (fm_fresh ly S ly2 S2 W2 memM mdM res HARM Hab2).
assert (HENVM : amf_env tfibsegs link_amf (rd W2 memM)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JM HENV0).
pose proof HENVM as (EThr & ENl & _).
refine (fm_E W2 W ly S mem md ly2 S2 sp0 regsM regs memM mdM res _ JM Hblk2 Hnew _ M8 _ M19 M20 MFR MZ
  (fm_mode_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JM VMODE0) EThr ENl MHD _).
- unfold spZ. rewrite M2. apply fm_w64u. lia.
- rewrite M9, fm_w64u by fmS. fmS.
- intros regs1 mem1 md1 J1 SB1 E10 E2 E8 E9 E18 E19 E20 EK E16 E8' EF EFR.
  assert (HENV1 : amf_env tfibsegs link_amf (rd W2 mem1)) by exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 HENV0).
  pose proof HENV1 as (_ & _ & ELock).
  refine (fm_F W2 W ly S mem md ly2 S2 sp0 regs1 mem1 md1 1 (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 1)) _
    J1 E10 _ (u64_range _) (u64_range _) _ E16 E8' ELock _).
  + unfold spZ. rewrite E2. apply fm_w64u. lia.
  + rewrite fm_w64_un. exact Hra.
  + intros regsF memF mdF JF SBF F1 F8 F2 F10 FK FVH FFR.
    pose proof JF as (_ & _ & _ & _ & _ & JFfr & _).
    pose proof (fm_sbm_fds _ _ SB1) as [Fd1 Fs1]. pose proof (fm_sbm_fds _ _ SBF) as [FdF FsF].
    assert (HIMGH : forall a, FM_HEAD <= a < FM_HEAD + 8 -> ~ (res <= a < res + 272)).
    { intros a Ha Hb.
      destruct (fm_head_img a Ha) as (Hi & _ & _).
      apply (blk_img tfibsegs B LAWS ly2 S2 W2 memM mdM res AMF_BLOCK a HARM Hblk2);
        [change (req_size AMF_BLOCK) with 1304; lia | exact Hi]. }
    assert (EFF : fm_wfile (rd W2 memF) res (getr regsM 9) (getr regsM 18)).
    { eapply fm_wfile_kept; [exact EF|]. intros a Ha. apply FFR; [lia|]. intros Hh. exact (HIMGH a Hh Ha). }
    rewrite M9, M18 in EFF.
    destruct (fm_amf (rd W2 memF) res ltac:(lia) ltac:(unfold AMF_BLOCK; lia) Hf16 EFF) as [HK HD].
    unfold afm_w_post. exists ly2, S2, regsF, memF, mdF, res.
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
    split; [rewrite F10; exact E8|].
    split; [exact JFfr|].
    split; [exact Hmo2|].
    split; [rewrite FdF, Fd1; exact Fd|].
    split; [rewrite FsF, Fs1; exact Fs|].
    split; [exact Hf4|].
    split; [exact Hf16|].
    split; [exact Hab2|].
    split; [exact HK|].
    split; [exact HD|].
    split; [rewrite E8, fm_w64u in FVH by lia; exact FVH|].
    split; [exact (fm_env_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JF HENV0) | exact HWILD].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 6. THE CONTRACT, on link's ASan image, at fmemopen's entry 0x96a1c, ra 0x96ab8, window           *)
(*    [0x10360, 0x10380).                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)
Theorem fo_musl_ok :
  afmemopen_w_spec link_asink_head tfibsegs B link_amf MT CTX LA_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.
Proof.
unfold afmemopen_w_spec. intros W ly S regs mem md ch Hpre.
destruct Hpre as (_ & HFN & Hsp & (G10 & G11 & G12 & VMW & GRWA & HMCW & HENV0 & HHD0) & Hnev & Hlive & Hmo
  & Huni0 & Huni).
change (amf_buf link_amf) with 0x62fee0 in G10. change (amf_size link_amf) with 4096 in G11.
change (amf_ofl_head link_amf) with FM_HEAD in HHD0.
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
assert (FS : STK = 16432) by reflexivity. rewrite FS in Hslo.
set (sp0 := spZ regs) in *.
assert (HJ0 : AJ STK sp0 FPT ly S W mem md [] ly S W mem md 0)
  by (eapply ajournal_init; first [exact HFN | exact LAWS | exact fm_segs_low]).
pose proof mc_bounds as [MB1 MB2].
assert (HSA0 : fm_sargs W mem).
{ split; [exact VMW|]. split; [exact GRWA|]. intros a Ha. rewrite MB1, MB2 in Ha. exact (HMCW a Ha). }
assert (VMODE0 : val_mem tfibsegs (rd W mem) FM_MODE 1 119) by exact (fm_mode1 _ VMW).
(* A: entry to strchr(mode, '+'). *)
apply (fm_A W W ly S mem md regs mem md _ HJ0 G12).
intros regs1 mem1 md1 J1 SB1 A1 A2 A10 A11 A8 A9 A18 A19 A20 AK AFR AMB.
assert (HSA1 : fm_sargs W mem1).
{ apply (fm_cells W mem mem1 HSA0). intros a Ha. apply (fm_av_mb W W mem mem1 a). apply AMB; lia. }
assert (SP1 : spZ regs1 = sp0 - 48) by (unfold spZ; rewrite A2; apply fm_w64u; lia).
apply (fm_strchr_step FM_MODE 43 0 W W ly S mem md regs1 mem1 md1 sp0 _ ltac:(right; left; reflexivity) J1 SP1).
{ rewrite A1. apply AE2y.ret_ok_lit; [unfold FM_RA1; lia | reflexivity]. }
{ exact A10. }
{ exact A11. }
{ exact HSA1. }
intros regs2 mem2 md2 J2 SB2 P10 P1 P2 PK2 PAV.
unfold FSC_WIN in PAV.
replace (raZ regs1) with FM_RA1 by (unfold raZ; rewrite A1; symmetry; apply fm_w64u; unfold FM_RA1; lia).
assert (HSA2 : fm_sargs W mem2).
{ apply (fm_cells W mem1 mem2 HSA1). intros a Ha. apply PAV; lia. }
(* B: strchr returned 0; to strchr("rwa", 'w'). *)
apply (fm_B W W ly S mem md sp0 regs2 mem2 md2 _ J2 P10).
{ rewrite (fm_kl _ _ _ 19 19%bv PK2 ltac:(fmP) ltac:(fmB)). exact A19. }
{ exact (fm_mode1 _ (proj1 HSA2)). }
intros regs3 mem3 md3 J3 SB3 B1 B10 B11 B19 B20 B2 B8 B9 B18 BK BMB.
assert (SP3 : spZ regs3 = sp0 - 48) by (unfold spZ; rewrite B2, P2; exact SP1).
assert (HSA3 : fm_sargs W mem3).
{ apply (fm_cells W mem2 mem3 HSA2). intros a Ha. apply (fm_av_mb W W mem2 mem3 a). apply BMB. lia. }
apply (fm_strchr_step FM_RWA 119 (FM_RWA + 1) W W ly S mem md regs3 mem3 md3 sp0 _ ltac:(left; reflexivity) J3 SP3).
{ rewrite B1. apply AE2y.ret_ok_lit; [unfold FM_RA2; lia | reflexivity]. }
{ exact B10. }
{ exact B11. }
{ exact HSA3. }
intros regs4 mem4 md4 J4 SB4 T10 T1 T2 TK TAV.
unfold FSC_WIN in TAV.
replace (raZ regs3) with FM_RA2 by (unfold raZ; rewrite B1; symmetry; apply fm_w64u; unfold FM_RA2; lia).
(* C: strchr returned "rwa" + 1; to the malloc call. *)
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
(* the malloc call: amalloc04_rule_d through fm_malloc_d. Its trace is a fixed row of the universe (the two
   universe premises, YCbq.v call_trace_in), so its depot step adds no wild trace (depot_step_fixed_wild). *)
assert (HU5 : In (call_trace0 (pc_malloc_ra0 (as_code B)) regs5 ch) (as_universe B)).
{ rewrite call_trace_of_spine.
  replace (raZ regs5) with LA_FM_MALLOC_RA by (unfold raZ; rewrite C1'; symmetry; apply fm_w64u; unfold LA_FM_MALLOC_RA; lia).
  exact (Huni _ Hsp). }
assert (HTR : In (call_trace ly (pc_malloc_ra0 (as_code B)) regs5 ch) (u_fix (as_universe B)))
  by exact (call_trace_in ly _ regs5 ch _ Huni0 HU5).
pose proof (ts_code B TB) as TC.
unfold cfg_at. replace (w64 FM_MALLOC) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite TC; reflexivity).
eapply SRr_bind.
{ apply (fm_malloc_d W regs5 mem5 STK sp0 FPT ly S W mem md [] ly S md5 0 AMF_BLOCK (-48) (w64 LA_FM_MALLOC_RA) ch J5 C10).
  - exact amf_block_size_ok.
  - exact Hlive.
  - rewrite SP5. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. rewrite FS. lia.
  - rewrite (fm_kl _ _ _ 3 3%bv KP5 ltac:(fmP) ltac:(fmB)). exact Hgp.
  - rewrite (fm_kl _ _ _ 4 4%bv KP5 ltac:(fmP) ltac:(fmB)). exact Htp.
  - exact C1'.
  - apply AE2y.ret_ok_lit; [unfold LA_FM_MALLOC_RA; lia | reflexivity].
  - lia.
  - apply (achain_chain_pre ly _ sp0 (s0Z regs) ch regs5).
    + apply (achain_kept ly (aview tfibsegs (w_H W) mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
      intros a Ha. pose proof J5 as (_ & _ & _ & _ & _ & _ & _ & _ & J5F1 & _). apply J5F1; [lia|]. rewrite FS. lia.
    + rewrite SP5. lia.
    + unfold s0Z. rewrite S08. reflexivity.
    + unfold raZ. rewrite C1', fm_w64u; unfold LA_FM_MALLOC_RA; lia.
  - exact HU5.
  - exact Hmo. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs6 & mem6 & md6 & res & -> & J6 & HPR6 & U10 & Hfr6 & Hres & Hab2 & HCK & Hmo2
  & Fd6 & Fs6 & DEP6).
assert (HWILD : (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot S)))%nat)
  by exact (depot_step_fixed_wild (as_universe B) _ _ _ DEP6 HTR).
pose proof HCK as (K1 & _ & K3 & _).
unfold ASTACK in K1.
pose proof J6 as (HAR6 & _).
assert (Hblk6 : In (res, AMF_BLOCK) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem6 md6 res AMF_BLOCK HAR6 Hblk6) as (Hf16 & Hf4 & Hfceil & Hfapp & _).
change (req_size AMF_BLOCK) with 1304 in Hfceil, Hfapp.
assert (Hnew : ~ In (res, AMF_BLOCK) (ablocks B ly S)) by exact (fm_fresh ly S ly2 S2 W2 mem6 md6 res HAR6 Hab2).
unfold aregs_preserved in HPR6.
change (mkCfg (mkst regs6 (w64 LA_FM_MALLOC_RA) mem6 (seg_rom tfibsegs)) md6) with (cfg_at tfibsegs LA_FM_MALLOC_RA regs6 mem6 md6).
(* D: malloc returned res >= 4096 (the NULL arm 0x96abc is refuted here); to the memset call. *)
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
    + right. right. left. exists res, AMF_BLOCK. split; [exact Hblk6|]. split; [exact Hnew|].
      change (req_size AMF_BLOCK) with 1304. lia.
    + unfold ESTACK. lia.
  - clear - Hfapp Hf4 C1. unfold in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem7 md7 res AMF_BLOCK res 272 HAR7 Hblk6);
      [lia | change (req_size AMF_BLOCK) with 1304; lia].
  - intros _. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem7 md7 res AMF_BLOCK res 272 HAR7 Hblk6);
      [lia | change (req_size AMF_BLOCK) with 1304; lia | lia].
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
  destruct (fm_head_img a Ha) as (Hi & Hns & He).
  rewrite MFR8; [| unfold FM_HEAD in Ha; lia | | unfold FM_HEAD in Ha; lia].
  2: { intros Hb. apply (blk_img tfibsegs B LAWS ly2 S2 W2 mem6 md6 res AMF_BLOCK a HAR6 Hblk6);
         [change (req_size AMF_BLOCK) with 1304; lia | exact Hi]. }
  rewrite (fm_av_mb W2 W2 mem6 mem7 a (DMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite K3 by assumption. rewrite (fm_av_mb W W mem4 mem5 a (CMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite TAV by (unfold FM_HEAD in Ha; lia). rewrite (fm_av_mb W W mem2 mem3 a (BMB a ltac:(unfold FM_HEAD in Ha; lia))).
  rewrite PAV by (unfold FM_HEAD in Ha; lia).
  exact (fm_av_mb W W mem mem1 a (AMB a ltac:(unfold FM_HEAD in Ha; lia) ltac:(unfold FM_HEAD in Ha; lia))). }
pose proof (fm_sbm_fds _ _ SB1) as [Fd1 Fs1]. pose proof (fm_sbm_fds _ _ SB2) as [Fd2 Fs2].
pose proof (fm_sbm_fds _ _ SB3) as [Fd3 Fs3]. pose proof (fm_sbm_fds _ _ SB4) as [Fd4 Fs4].
pose proof (fm_sbm_fds _ _ SB5) as [Fd5 Fs5]. pose proof (fm_sbm_fds _ _ SB7) as [Fd7 Fs7].
pose proof (fm_sbm_fds _ _ SB8) as [Fd8 Fs8].
apply (fm_tail W W2 ly S mem md ly2 S2 regs regs8 mem8 md8 res J8 Hab2 Hmo2).
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
- eapply fm_vm_fr; [|exact HHD0]. intros x Hx. apply mbyte_of_aview. apply HD. simpl Z.of_nat in Hx. lia.
- exact HENV0.
- exact VMODE0.
- exact HWILD.
Qed.

End W.

About fo_musl_ok.
Print Assumptions fo_musl_ok.
