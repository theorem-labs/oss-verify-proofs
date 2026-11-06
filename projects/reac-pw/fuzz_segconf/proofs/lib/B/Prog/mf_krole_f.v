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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 301 of its 359 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KROLE, piece kr_s_fold: from
   the inner point KR_FOLD 0x86728 (ieq "role" answered 1) through the call of fold to KR_WORDS 0x86758 with i = 0
   (lib/B/Prog/mf_krole_m.v). A sub-lane of a walk lane of the image-B m_file-family owner's G2B. proves no function (kind: segment lemma
   of m_file's walk, S_MF_KROLE piece kr_s_fold).

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 380-391):
     86728 ld a0,192(s1)      a0 = v = p + ov (the value's first byte in the text, the K cut's 192(s1))
     8672c li a3,64           a3 = cap = 64
     86730 mv a1,s10          a1 = vl
     86734 ld a2,144(s1)      a2 = low = FB + 32 (mf_cells' 144(s1))
     86738 jal fold           lib/B/Prog/fold_c.v through m_file_fold.v's mf_fold_call: a0 = |fold_out (zb vv) 64| =
                              kr_ln vl, low holds kr_low vv and its NUL
     8673c mv s10,a0          s10 = kr_ln vl
     86740 li s4,0            s4 = 0 = -(4 * 0)
     86744 auipc a0 / 86748 addi s9,a0   s9 = 0x211e0 = &m_key.role (listing object 18, SegInstB.rolesA)
     8674c ld s5,80(s1)       s5 = WORDS (object 15, SegInstB.wordsA; mf_cells' 80(s1))
     86750 mv s8,s5           s8 = WORDS
     86754 ld s7,72(s1)       s7 = SHADOW_OFF + WORDS / 8 (mf_cells' 72(s1), (A_OBJ 15 >> 3) + SB)
   then KR_WORDS 0x86758 with i = 0. No instruction of the piece is instrumented (no shadow check, no UBSan trap):
   the four loads are frame-cell loads.

   THE PROOF: two runs from m_file_sd.v's seed with every region read-only (the slot window closed), so the memory at
   each stop is the start's (m_file_k.v mf_keep_run0 carries the cut facts). The first run (the slot 192(s1) as atom
   52 = p + ov) stops at fold's entry; m_file_fold.v's mf_fold_call takes the call, with the value's bytes l = zb vv
   (the vl bytes [ov, ov + vl) of the text left: mk_kv, mf_loop's sa_str / sa_addr, mf_txt_heap_now for sa_heap);
   its continuation gives every cut fact at the returned state, a0 = kr_ln vl (fold_c.v fold_out_length,
   mf_krole_m.v kr_ln_min) and low.i's first kr_ln vl + 1 bytes = kr_low vv ++ [0]. The second run, from a fresh seed
   at 0x8673c, sets the loop's registers; KR_WORDS_stmt at i = 0 ends it (kr_word_go_0). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k fold_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_fold.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_krole_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* 0x8673c, fold's return point (listing offset AF_m_file + 0x5fc) *)
Definition KF_RET : Z := AF_m_file + 0x5fc.
(* the piece's regions: m_file_sd.v's mf_regions (cells, np, low.i in scope, the caller's slot chunks slx) with the
   slot window closed: every region read-only *)
Definition kf_rs (slx : list YP09.chunk) : smem :=
  list_upd (mf_regions true true slx false false [] false MF_LOW_ON) 1 (set_window (mf_r_slots true true slx) 0 0).
Definition kf_ss (pc : Z) (slx : list YP09.chunk) : sstate := mkSS pc sr_mf (kf_rs slx) None mf_facts.
(* the K cut's 192(s1) (the value's address p + ov) as the caller's first extra atom, 52 *)
Definition kf_c192 : YP09.chunk := YP09.mkChunk 192 (CVal 8 (SOff 52 0)).

(* ===================================== the value's bytes ===================================== *)
(* the line is a prefix of the text left *)
Lemma kf_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.
(* the list Z read at a through an ASan reader, as list byte, and back *)
Lemma kf_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (sa_aview_rng segs H mem _ _ (HZ i Hi)). }
split; [|exact HR].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.
(* and the other way: bytes of a list Z in range read as that list Z *)
Lemma kf_zs_of_bytes : forall (rd : reader) a (l : list Z), Forall (fun z => 0 <= z < 256) l ->
  sa_bytes rd a (seg_spec.zb l) -> sa_zs rd a l.
Proof.
intros rd a l HR H i Hi.
assert (Hi' : (i < length (seg_spec.zb l))%nat) by (unfold seg_spec.zb; rewrite length_map; exact Hi).
rewrite (H i Hi'). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.
Lemma kf_forall_firstn : forall {A} (P : A -> Prop) j l, Forall P l -> Forall P (firstn j l).
Proof. intros A P j l H. rewrite <- (firstn_skipn j l) in H. apply Forall_app in H as [H _]. exact H. Qed.
(* the folded value and its NUL are bytes *)
Lemma kf_low_rng : forall vv, Forall (fun z => 0 <= z < 256) vv ->
  Forall (fun z => 0 <= z < 256) (kr_low vv ++ [0]).
Proof.
intros vv H. apply Forall_app. split; [|constructor; [lia | constructor]].
apply Forall_forall. intros z Hz. unfold kr_low, h_fold in Hz. apply in_map_iff in Hz as (x & <- & Hx).
apply kr_lower_byte. exact (proj1 (Forall_forall _ _) (kf_forall_firstn _ _ _ H) x Hx).
Qed.
(* fold's text at cap 64 on the bytes zb vv is m_key's h_fold vv 64 *)
Lemma kf_fold_out : forall vv, Forall (fun z => 0 <= z < 256) vv -> fold_out (seg_spec.zb vv) 64 = kr_low vv.
Proof. intros vv H. unfold fold_out, kr_low. rewrite (sa_zs_zb vv H). reflexivity. Qed.

(* ===================================== the run tactics ===================================== *)
(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac kf_awr :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* name the model after a run (fuzz_command check_reply_s2.v cr2_name_md) *)
Ltac kf_name_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => let m := fresh "mdq" in set (m := d) in *; clearbody m end.
(* after a run from a read-only state: its memory is the run's start memory, composed into KM (the memory at the
   run's start) *)
Ltac kf_mem KM :=
  lazymatch goal with HF : frame_of ?Ex ?rs ?m0 (ms_mem ?msc) |- _ =>
    let Kn := fresh "Kn" in
    assert (Kn : forall x, ms_mem msc x = m0 x)
      by (let x := fresh "x" in let rr := fresh "rr" in let Hi := fresh "Hi" in let Hw := fresh "Hw" in
          intros x; apply HF; intros (rr & Hi & Hw); revert Hw; vm_compute in Hi;
          repeat (destruct Hi as [<- | Hi]; [cbn; lia |]); destruct Hi);
    let KM' := fresh "KM" in
    pose proof (fun x => eq_trans (Kn x) (KM x)) as KM';
    clear Kn KM; rename KM' into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    try (lazymatch m0 with ms_mem ?old => clear old end);
    try (rename msc into ms)
  end.
(* a register the run left alone: its value at the stop is its value at the start, both the same symbolic value
   (check_reply_s2.v cr2_reg_eq) *)
Ltac kf_req HS0 HS :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
      transitivity (sv_denot Ev (sr_get (ss_regs ss) r)); [exact (st_ok_pi_restrict_reg H Ev ss ms r HS)|]
  | st_ok ?sg ?Ev ?ss (restrict ?H ?ms) =>
      transitivity (sv_denot Ev (sr_get (ss_regs ss) r)); [exact (st_ok_restrict_reg sg H Ev ss ms r HS)|]
  end;
  lazymatch type of HS0 with st_ok_pi _ _ ?Ev0 ?ss0 (restrict ?H0 ?ms0) =>
  etransitivity; [| symmetry; exact (st_ok_pi_restrict_reg H0 Ev0 ss0 ms0 r HS0)];
  f_equal; vm_compute; reflexivity end end.
Ltac kf_regs_pres HS0 HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [-> | Hc]; [kf_req HS0 HS |]); subst r; kf_req HS0 HS.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the shared Section hypotheses (section 2 of the KROLE piece plan) this piece uses *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* fold at its listing entry, at every FP state (lib/B/Prog/fold_c.v; m_file_fold.v's mf_fold_call takes it) *)
Hypothesis FOLD : forall fx0 : YK11.FPState, fold_contract (fx := fx0) SEGS B (BASE + AF_fold) SegInstB.STK_fold.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the value's vl bytes [ov, ov + vl) of the text left at p + ov: what mf_fold_call asks of s *)
Lemma kf_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest ov vl,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (ov + vl <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat ov) (seg_spec.zb (firstn vl (skipn ov rest))) /\
  Forall (fun z => 0 <= z < 256) (firstn vl (skipn ov rest)) /\
  Z.of_nat (length (seg_spec.zb (firstn vl (skipn ov rest)))) = Z.of_nat vl /\
  sa_addr (rdW Wc memc) (p + Z.of_nat ov) (Z.of_nat vl) /\
  sa_heap B lyc Sc (p + Z.of_nat ov) (Z.of_nat vl) /\ p + Z.of_nat ov <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest ov vl CX CORE LOOP Hovl.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & _) & _) & LADDR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat ov) (firstn vl (skipn ov rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  rewrite nth_firstn. destruct (Nat.ltb_spec i vl) as [_|Hc]; [|lia]. rewrite nth_skipn.
  replace (p + Z.of_nat ov + Z.of_nat i) with (p + Z.of_nat (ov + i)) by lia.
  pose proof (LZ (ov + i)%nat ltac:(rewrite length_app; cbn [length]; lia)) as E.
  rewrite app_nth1 in E by lia. exact E. }
destruct (kf_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HR).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bb & bm & Hin & Hb1 & Hb2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bb bm HAR Hin) as (_ & B4096 & _).
split; [exact HB|]. split; [exact HR|]. split.
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
split.
{ apply (fd_addr_prefix _ _ (Z.of_nat vl + 1)); [|lia].
  apply (mf_addr_sub _ p (Z.of_nat (length rest) + 1)); [exact LADDR | lia | lia | lia]. }
split.
{ exists bb, bm. split; [exact Hin|]. lia. }
lia.
Qed.

(* the piece's symbolic state at pc: mf_seed's (cells, np in 152(s1), low.i in scope, the extra atoms xs, the slot
   chunks slx) with the slot window closed (check_reply_s7.v cr7_seed's form) *)
Lemma kf_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi p rest xs slx pc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 -> mf_np v memc Wc (mf_next p rest) ->
0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64 -> 0 <= mf_next p rest < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos (Some gi) (mf_next p rest) xs) (mrestrict (w_H Wc) memc)
  (mf_s1 (mv_sp v))) slx ->
regions_wf (mf_regions true true slx false false [] false MF_LOW_ON) = true ->
regions_wf (kf_rs slx) = true ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) xs) (kf_ss pc slx)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi p rest xs slx pc CX CORE CELLS RA NP HC HN FS HWF HWF'.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) xs pc
  true true slx false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) HC (fun _ => NP)
  HN ltac:(unfold MF_LOW_ON; lia) FS (Forall_nil _) HWF) as HS.
pose proof (st_ok_pi_region_nth _ _ _ 1 (mf_r_slots true true slx) HS eq_refl) as Hr.
exact (ast_ok_pi_set_region _ _ _ 1 (mf_r_slots true true slx) (set_window (mf_r_slots true true slx) 0 0) HS eq_refl
  eq_refl HWF' (region_ok_rewindow SEGS _ _ _ 0 0 Hr ltac:(intros o Ho; lia))).
Qed.

(* 0x8673c, fold's return: s10 = a0 = kr_ln vl, the loop's registers set, to KR_WORDS with i = 0 *)
Lemma kf_ret : forall n v lyc Sc Wc regs2 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
KR_WORDS_stmt B n ->
kr_cx B n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> mf_regs_at B v lyc pos regs2 ->
kr_low_at lyc pos Wc memc (kr_low vv ++ [0]) ->
getr regs2 10 = w64 (Z.of_nat (kr_ln vl)) -> getr regs2 27 = w64 (line + 1) ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + KF_RET)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros n v lyc Sc Wc regs2 memc mdc pos mcc gi line p rest ok kl ov vl k vv WORDS KCX RA LOW R10 R27.
pose proof KCX as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & KV & FIN & NP & HIE).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as HC.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as HN.
pose proof (kf_seed v lyc Sc Wc regs2 memc mdc pos mcc gi p rest [] [] KF_RET CX CORE CELLS RA NP HC HN (Forall_nil _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
remember (mfE regs2 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr regs2 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) [])
  (Z_to_bv 64 0)) by (subst E; intros; apply mfE_extra; assumption).
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstB.wordsA)
  by (subst E; rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia); rewrite (mf_words_obj VOBJS); reflexivity).
assert (ER : ew E (A_OBJ MF_ROLES_OBJ) = Z_to_bv 64 SegInstB.rolesA)
  by (subst E; rewrite mfE_img by (unfold A_OBJ, MF_ROLES_OBJ, A_TEXT, A_LIM; lia); rewrite (mf_roles_obj VOBJS); reflexivity).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (KM : forall x, memc x = memc x) by reflexivity.
pose proof CORE as (HJ & _).
pose proof HS as HS0.
(* 0x8673c-0x86754: s10, s4, s9, s5, s8, s7; a run to KR_WORDS *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_WORDS; [kf_awr|].
kf_mem KM. kf_name_md.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & _) & R19 & _).
assert (X2 : getr (ms_regs ms) 2 = getr regs2 2) by kf_req HS0 HS.
assert (X3 : getr (ms_regs ms) 3 = getr regs2 3) by kf_req HS0 HS.
assert (X4 : getr (ms_regs ms) 4 = getr regs2 4) by kf_req HS0 HS.
assert (X8 : getr (ms_regs ms) 8 = getr regs2 8) by kf_req HS0 HS.
assert (X9 : getr (ms_regs ms) 9 = getr regs2 9) by kf_req HS0 HS.
assert (X18 : getr (ms_regs ms) 18 = getr regs2 18) by kf_req HS0 HS.
assert (X19 : getr (ms_regs ms) 19 = getr regs2 19) by kf_req HS0 HS.
assert (X27 : getr (ms_regs ms) 27 = getr regs2 27) by kf_req HS0 HS.
prreg HS (26%bv : bv 5) Q26. prreg HS (20%bv : bv 5) Q20.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms (25%bv : bv 5) HS) as Q25.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms (21%bv : bv 5) HS) as Q21.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms (24%bv : bv 5) HS) as Q24.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms (23%bv : bv 5) HS) as Q23.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let e25 := eval vm_compute in (sr_get (ss_regs ss) (25%bv : bv 5)) in
  let e21 := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
  let e24 := eval vm_compute in (sr_get (ss_regs ss) (24%bv : bv 5)) in
  let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
  change (sr_get (ss_regs ss) (25%bv : bv 5)) with e25 in Q25;
  change (sr_get (ss_regs ss) (21%bv : bv 5)) with e21 in Q21;
  change (sr_get (ss_regs ss) (24%bv : bv 5)) with e24 in Q24;
  change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23 end.
assert (HWv : SegInstB.wordsA = 0xa2040) by reflexivity.
assert (HRv : SegInstB.rolesA = 0x211e0) by reflexivity.
pose proof (mf_denot_shx E (A_OBJ MF_WORDS_OBJ) SegInstB.wordsA 0 EW E32
  ltac:(rewrite HWv; lia) ltac:(lia) ltac:(rewrite HWv; lia)) as D23.
pmkst HS.
(* the KDISP facts at the run's memory (it changed no byte) *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
  assert (Kall : forall a, rdW Wc mm a = rdW Wc memc a)
    by (intros a; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
    as (CORE' & CELLS' & NPk & LOOPk) end.
assert (LOW' : kr_low_at lyc pos Wc (ms_mem ms) (kr_low vv ++ [0])).
{ unfold kr_low_at in LOW |- *. intros i Hi. rewrite Kall. exact (LOW i Hi). }
pose proof (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hne (conj (LOOPk _ _ _ _ _ LOOP)
  (conj KV (conj FIN (conj (NPk _ NP) HIE))))))))))) as KCX'.
assert (RB' : kr_regs_b B v (ms_regs ms)).
{ unfold kr_regs_b. rewrite X2, X3, X4, X8, X9, X18, X19.
  refine (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R18 R19)))))). }
apply (WORDS v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc gi line p rest ok kl ov vl k vv 0%nat KCX' RB'
  ltac:(lia) LOW' (kr_word_go_0 _)).
- rewrite Q26, (EE 10%nat 10%bv eq_refl). exact R10.
- rewrite X27. exact R27.
- rewrite Q20. unfold w64. f_equal; lia.
- rewrite Q25, denot_lit_U. unfold w64. f_equal;
  transitivity SegInstB.rolesA; [exact (U_atom E _ SegInstB.rolesA ER ltac:(rewrite HRv; lia)) | lia].
- rewrite Q21, denot_lit_U. unfold w64. f_equal;
  transitivity SegInstB.wordsA; [exact (U_atom E _ SegInstB.wordsA EW ltac:(rewrite HWv; lia)) | lia].
- rewrite Q24, denot_lit_U. unfold w64. f_equal;
  transitivity SegInstB.wordsA; [exact (U_atom E _ SegInstB.wordsA EW ltac:(rewrite HWv; lia)) | lia].
- rewrite Q23. etransitivity; [exact D23|]. unfold w64. f_equal; cbn [Z.of_nat]; rewrite ?Z.add_0_r; reflexivity.
Qed.

(* KR_FOLD 0x86728: a0 = v, a3 = 64, a1 = vl, a2 = low; fold (m_file_fold.v mf_fold_call), then kf_ret *)
Lemma kr_s_fold : forall n, KR_WORDS_stmt B n -> KR_FOLD_stmt B n.
Proof.
intros n WORDS. unfold KR_FOLD_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KCX RA S192 R21 R26 R27.
pose proof KCX as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & KV & FIN & NP & HIE).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & Hcur & _).
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (kf_line_le rest) as Hml.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as HC.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as HN.
unfold mf_slot in S192.
assert (FS : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov])
  (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) [kf_c192]).
{ constructor; [|constructor]. unfold kf_c192.
  apply (mf_chunk_atom _ _ _ 192 52 0 (p + Z.of_nat ov)).
  - exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)).
  - lia.
  - lia.
  - rewrite Z.add_0_r. exact S192. }
pose proof (kf_seed v lyc Sc Wc regs1 memc mdc pos mcc gi p rest [p + Z.of_nat ov] [kf_c192] KR_FOLD CX CORE CELLS RA
  NP HC HN FS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov]) as E eqn:HE.
assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov]) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat ov))
  by (subst E; exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) _ 0 ltac:(unfold A_TEXT; lia))).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. cbn [Nat.add nth mf_extra map app] in E34.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hfin) as (F1 & F2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (KM : forall x, memc x = memc x) by reflexivity.
pose proof HS as HS0.
unfold mf_at.
(* 0x86728-0x86738: a0 = 192(s1), a3 = 64, a1 = s10, a2 = 144(s1); the jal *)
paj_run_tok RUN HS HJ SHOK Bspan; [kf_awr|].
kf_mem KM. kf_name_md.
assert (HPc : aregs_preserved regs1 (ms_regs ms)) by (kf_regs_pres HS0 HS).
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13.
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10' : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)) by (rewrite Q10, E52; reflexivity).
assert (Q11' : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)) by (rewrite Q11, (EE 26%nat 26%bv eq_refl); exact R26).
assert (Q12' : getr (ms_regs ms) 12 = w64 (frame_addr lyc 1 pos + 32))
  by (rewrite Q12, E34, unsigned_lit_small by lia; reflexivity).
assert (Q13' : getr (ms_regs ms) 13 = w64 64) by (rewrite Q13; reflexivity).
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KF_RET)) by (rewrite Q1; reflexivity).
pmkst HS.
(* the jal's target *)
rewrite (SIGP SS_fold ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_fold) with AF_fold by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
    as (CORE' & CELLS' & NPk & LOOPk) end.
pose proof (NPk _ NP) as NP'. pose proof (LOOPk _ _ _ _ _ LOOP) as LOOP'.
destruct (kf_slice_facts v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
  ltac:(lia)) as (SB & SR & SL & SA & SH & S0).
rewrite KV4 in SB, SR, SL.
refine (mf_fold_call B FOLD (mf_chain B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc (Some gi) line p rest
  (mf_next p rest) KF_RET
  (p + Z.of_nat ov) (Z.of_nat vl) 64 (seg_spec.zb vv) CX LS CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1' _ _
  Q10' Q11' Q12' Q13' ltac:(lia) S0 SB SL SA SH _).
- unfold KF_RET, AF_m_file; lia.
- unfold KF_RET, AF_m_file; reflexivity.
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 LOW2 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite (fold_out_length (seg_spec.zb vv) 64 ltac:(lia)), SL, <- kr_ln_min in A02.
  rewrite (kf_fold_out vv SR) in LOW2.
  apply (kf_ret n v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv WORDS
    (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hne (conj LOOP2 (conj KV (conj FIN
      (conj NP2 HIE)))))))))))
    (mf_regs_keep B v lyc pos regs1 regs2 RA HP12)).
  + unfold kr_low_at. exact (kf_zs_of_bytes _ _ _ (kf_low_rng vv SR) LOW2).
  + exact A02.
  + rewrite <- R27. exact (HP12 27 ltac:(unfold acallee_saved; lia)).
Qed.
End e.
End f.
End d.

About kr_s_fold.
Print Assumptions kr_s_fold.
