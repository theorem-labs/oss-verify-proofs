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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 351 of its 411 lines of code are new or changed and 393 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD, piece i: from the inner
   cut MK_IRET 0x86854 (ieq "model" answered; lib/B/Prog/mf_kmod_m.v MK_IRET_stmt) to the cut KIGN 0x86968 ("model"
   missed; lib/B/Prog/m_file_m.v MF_KIGN_stmt) or, through the call of fold, to the inner cut MK_FRET 0x86870
   (mf_kmod_m.v MK_FRET_stmt). A sub-lane of a walk lane of the image-B m_file-family owner's G2B. proves no function (kind: segment lemma
   of m_file's image-B walk, S_MF_KMOD piece i: MK_IRET 0x86854 to KIGN / MK_FRET).

   mk_iret_ok : forall n, MF_KIGN_stmt B n -> MK_FRET_stmt B n -> MK_IRET_stmt B n.

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 455-461):
     86854 beqz a0,86968     a0 = b2z (ieq k "model"): 0 goes to KIGN with "model" added to the words missed
     86858 ld a0,192(s1)     a0 = v = p + ov (the K cut's 192(s1))
     8685c li a3,24          a3 = cap = 24
     86860 mv a1,s10         a1 = vl
     86864 ld s4,144(s1)     s4 = low = FB + 32 (mf_cells' 144(s1))
     86868 mv a2,s4          a2 = low
     8686c jal fold          lib/B/Prog/fold_c.v through m_file_fold.v's mf_fold_call: a0 = |fold_out (zb vv) 24| =
                             |h_fold vv 24|, low holds h_fold vv 24 and its NUL; back at 0x86870 = MK_FRET
   No instruction of the piece is instrumented (no shadow check) and none is a UBSan trap branch: the two loads are
   frame-cell loads, the one branch is the `beqz` on ieq's answer.

   THE MODEL: ieq k "role" = false (the K cut's missed list) and ieq k "model" = true make the cut's mk_disp the
   model arm mk_mod (mf_kmod_t.v mkt_disp_model); ieq k "model" = false adds "model" to the words missed (KIGN).

   THE PROOF: a0 is pinned to its value 0 or 1 (st_ok_pi_pin_reg'), so the token executor decides the `beqz`.
   - 0 (mi_ign): one run from m_file_sd.v's seed with its regions dropped (the `beqz` reads no memory) to KIGN; the
     memory at the stop is the start's (m_file_k.v mf_keep_run0), every callee-saved register the start's.
   - 1 (mi_fold): one run from the seed with every region read-only (the frame cells, with 192(s1) as the extra atom
     52 = p + ov) to fold's entry; m_file_fold.v's mf_fold_call takes the call with the value's bytes l = zb vv (the
     vl bytes [ov, ov + vl) of the text left: mk_kv, mf_loop's sa_str / sa_addr, mf_txt_heap_now for sa_heap) and
     cap 24; its continuation gives every cut fact at the returned state (the same FP state), a0 = |h_fold vv 24|
     (fold_out (zb vv) 24 = h_fold vv 24 for bytes) and low.i's first |h_fold vv 24| + 1 bytes = h_fold vv 24 ++ [0];
     s4 = low and s11 = line + 1 are callee-saved, so MK_FRET_stmt closes the piece. ~ In 0 vv and the byte range of
     vv come from the text (sa_str's NUL-free bytes, the reader's byte range).
   Adapted from the image-B m_file-family owner's compiled image-B pieces mf_krole_d.v kd_ret (commit
   49f97829985c: the `beqz` on ieq's answer to a K cut) and mf_krole_f.v kr_s_fold (commit
   5dd1ad0a0ebe: the fold call at 0x86738), and from image A's mka_after (commit c1e1a58468c5,
   lib/A/Prog/m_file_s_kmod_a.v).
   Section hypotheses (the KMOD piece plan's texts): VOBJS (the seed), SIGP (the jal's target SIGMA SS_fold = BASE +
   AF_fold), FOLD (fold_contract at every FP state, mf_fold_call's callee); mf_fold_call's KCHAIN is m_file_k.v's
   mf_chain, which needs none. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq fold_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_fold.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_t mf_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the piece's regions for the fold run: m_file_sd.v's mf_regions (cells, np, low.i in scope, the caller's slot chunks
   slx) with the slot window closed: every region read-only *)
Definition mi_rs (slx : list YP09.chunk) : smem :=
  list_upd (mf_regions true true slx false false [] false MF_LOW_ON) 1 (set_window (mf_r_slots true true slx) 0 0).
Definition mi_ss (pc : Z) (slx : list YP09.chunk) : sstate := mkSS pc sr_mf (mi_rs slx) None mf_facts.
(* the K cut's 192(s1) (the value's address p + ov) as the caller's first extra atom, 52 *)
Definition mi_c192 : YP09.chunk := YP09.mkChunk 192 (CVal 8 (SOff 52 0)).

(* ===================================== the model side ===================================== *)
Lemma mi_role : forall k, Forall (fun w => ieq k w = false) [S_role] -> ieq k S_role = false.
Proof. intros k H. inversion H; assumption. Qed.
(* the words missed at KIGN: "role" (the K cut's) and "model" (ieq's 0) *)
Lemma mi_missed : forall k, Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = false ->
  Forall (fun w => ieq k w = false) [S_role; S_model].
Proof. intros k H1 H2. constructor; [exact (mi_role k H1) | constructor; [exact H2 | constructor]]. Qed.
(* the line is a prefix of the text left *)
Lemma mi_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.
(* a slice of a NUL-free text is NUL-free *)
Lemma mi_nul_free : forall (rest : list Z) ov vl, ~ In 0 rest -> ~ In 0 (firstn vl (skipn ov rest)).
Proof.
intros rest ov vl H Hin. apply H. apply mkt_in_firstn in Hin.
rewrite <- (firstn_skipn ov rest). apply in_or_app. right. exact Hin.
Qed.
(* the list Z read at a through an ASan reader, as list byte, and its byte range *)
Lemma mi_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
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
Lemma mi_zs_of_bytes : forall (rd : reader) a (l : list Z), Forall (fun z => 0 <= z < 256) l ->
  sa_bytes rd a (seg_spec.zb l) -> sa_zs rd a l.
Proof.
intros rd a l HR H i Hi.
assert (Hi' : (i < length (seg_spec.zb l))%nat) by (unfold seg_spec.zb; rewrite length_map; exact Hi).
rewrite (H i Hi'). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.
(* the folded value and its NUL are bytes *)
Lemma mi_hfold_rng : forall vv, Forall (fun z => 0 <= z < 256) vv ->
  Forall (fun z => 0 <= z < 256) (h_fold vv 24 ++ [0]).
Proof.
intros vv H. apply Forall_app. split; [exact (mkt_hfold_range vv H) | constructor; [lia | constructor]].
Qed.
(* fold's text at cap 24 on the bytes zb vv is m_key's h_fold vv 24 *)
Lemma mi_fold_out : forall vv, Forall (fun z => 0 <= z < 256) vv -> fold_out (seg_spec.zb vv) 24 = h_fold vv 24.
Proof. intros vv H. unfold fold_out. rewrite (sa_zs_zb vv H). reflexivity. Qed.

(* ===================================== the run tactics ===================================== *)
(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac mi_awr :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* name the model after a run (fuzz_command check_reply_s2.v cr2_name_md) *)
Ltac mi_name_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => let m := fresh "mdq" in set (m := d) in *; clearbody m end.
(* after a run from a read-only state: its memory is the run's start memory, composed into KM (the memory at the
   run's start) *)
Ltac mi_mem KM :=
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
Ltac mi_req HS0 HS :=
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the shared Section hypotheses (the KMOD piece plan) this piece uses, verbatim *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis FOLD : forall fx0 : YK11.FPState, fold_contract (fx := fx0) SEGS B (BASE + AF_fold) SegInstB.STK_fold.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the value's vl bytes [ov, ov + vl) of the text left at p + ov: what mf_fold_call asks of s *)
Lemma mi_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest ov vl,
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
destruct (mi_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HR).
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

(* the fold run's symbolic state at pc: mf_seed's (cells, np in 152(s1), low.i in scope, the extra atoms xs, the slot
   chunks slx) with the slot window closed *)
Lemma mi_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi p rest xs slx pc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 -> mf_np v memc Wc (mf_next p rest) ->
0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64 -> 0 <= mf_next p rest < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos (Some gi) (mf_next p rest) xs) (mrestrict (w_H Wc) memc)
  (mf_s1 (mv_sp v))) slx ->
regions_wf (mf_regions true true slx false false [] false MF_LOW_ON) = true ->
regions_wf (mi_rs slx) = true ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) xs) (mi_ss pc slx)
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

(* the KIGN run's symbolic state at pc: the seed with its regions dropped (a run that touches no memory) *)
Lemma mi_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_regs_at B v lyc pos regs1 ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos None 0 []) (mkSS pc sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc pc CX CORE RA.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc None 0 [] pc false false [] false false []
  false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia) ltac:(intros Hf; discriminate Hf)
  ltac:(lia) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exact (st_ok_pi_submem _ (ss_mf pc false false [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _) eq_refl).
Qed.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED *)
Lemma mi_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* an 8-byte frame cell off(s1) is kept by a change outside a window [lo, hi) below s1 *)
Lemma mi_slot_keep : forall v (W W' : world SEGS) m m' lo hi off x,
  mf_cx B v -> hi <= mf_s1 (mv_sp v) -> 0 <= off -> off + 8 <= 216 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W' m' a = rdW W m a) ->
  mf_slot v m W off x -> mf_slot v m' W' off x.
Proof.
intros v W W' m m' lo hi off x CX Hhi Ho0 Ho8 K H. unfold mf_slot in *.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hc). destruct (mf_sp0 B v CX) as (_ & H47 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((C1 & C2) & C3). unfold YG0f.ASAN_CEIL in C1, C2, C3.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hc.
apply (iq_val_keep W W' m m' _ 8 x); [|exact H].
intros a Ha. change (Z.of_nat 8) with 8 in Ha. apply K; destruct Hs1 as [E1 | E1]; rewrite E1 in *; lia.
Qed.

(* ieq "model" = 0: the `beqz` goes to KIGN with "model" added to the words missed, every other register and every
   byte the cut's *)
Lemma mi_ign : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MF_KIGN_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = false ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_slot v memc Wc 208 (p + Z.of_nat ok) -> getr regs1 21 = w64 (Z.of_nat kl) ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) -> getr regs1 26 = w64 (Z.of_nat vl) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 0 ->
mf_at B v Wc regs1 memc mdc MK_IRET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KIGN CX LS FRM CORE CELLS RA LEN NE
  LOOP KV MISS HM FIN S208 R21 S192 R26 R27 NP A0.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mi_seed0 v lyc Sc Wc regs1 memc mdc pos mcc MK_IRET CX CORE RA) as HS1.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
clear HS1.
(* 0x86854 `beqz a0` with a0 = 0: taken, to KIGN 0x86968 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KIGN.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (mi_pres E _ regs1 v lyc pos None 0 [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with MF_KIGN by (unfold MF_KIGN, AF_m_file; reflexivity) end.
apply (KIGN v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE' CELLS'
  (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) LEN NE (LPk mcc (Some gi) line p rest LOOP) KV
  (mi_missed k MISS HM) FIN).
- exact (mi_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX (Z.le_refl _)
    ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S208).
- intros Hf. discriminate Hf.
- transitivity (getr regs1 21); [exact (HPc 21 ltac:(unfold acallee_saved; lia)) | exact R21].
- exact (mi_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 192 _ CX (Z.le_refl _)
    ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S192).
- transitivity (getr regs1 26); [exact (HPc 26 ltac:(unfold acallee_saved; lia)) | exact R26].
- transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
- exact (NPk _ NP).
Qed.

(* ieq "model" = 1: the `beqz` falls through; a0 = v, a3 = 24, a1 = vl, s4 = a2 = low; fold (m_file_fold.v
   mf_fold_call); MK_FRET at its return *)
Lemma mi_fold : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MK_FRET_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = true ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) -> getr regs1 26 = w64 (Z.of_nat vl) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 1 ->
mf_at B v Wc regs1 memc mdc MK_IRET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv FRET CX LS FRM CORE CELLS RA LEN NE
  LOOP KV MISS HM FIN S192 R26 R27 NP A0.
pose proof LOOP as (_ & _ & _ & ((_ & LNZ) & _) & (LA0 & LA1 & _) & Hcur & _).
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (mi_line_le rest) as Hml.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as HC.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as HN.
(* the model: ieq k "role" = false and ieq k "model" = true make mk_disp the model arm mk_mod *)
assert (FIN' : mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v).
{ rewrite <- (mkt_disp_model mcc gi k vv (line + 1) (mi_role k MISS) HM). exact FIN. }
(* the value lies in the NUL-free text *)
assert (NZ : ~ In 0 vv) by (rewrite <- KV4; exact (mi_nul_free rest ov vl LNZ)).
unfold mf_slot in S192.
assert (FS : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov])
  (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) [mi_c192]).
{ constructor; [|constructor]. unfold mi_c192.
  apply (mf_chunk_atom _ _ _ 192 52 0 (p + Z.of_nat ov)).
  - exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)).
  - lia.
  - lia.
  - rewrite Z.add_0_r. exact S192. }
pose proof (mi_seed v lyc Sc Wc regs1 memc mdc pos mcc gi p rest [p + Z.of_nat ov] [mi_c192] MK_IRET CX CORE CELLS RA
  NP HC HN FS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS1.
(* a0 = 1: the `beqz` is not taken *)
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
clear HS1.
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
(* 0x86854-0x8686c: the `beqz` falls through, a0 = 192(s1), a3 = 24, a1 = s10, s4 = 144(s1), a2 = s4; the jal *)
paj_run_tok RUN HS HJ SHOK Bspan; [mi_awr|].
mi_mem KM. mi_name_md.
(* the registers the run left alone *)
assert (X2 : getr (ms_regs ms) 2 = getr regs1 2) by mi_req HS0 HS.
assert (X3 : getr (ms_regs ms) 3 = getr regs1 3) by mi_req HS0 HS.
assert (X4 : getr (ms_regs ms) 4 = getr regs1 4) by mi_req HS0 HS.
assert (X8 : getr (ms_regs ms) 8 = getr regs1 8) by mi_req HS0 HS.
assert (X9 : getr (ms_regs ms) 9 = getr regs1 9) by mi_req HS0 HS.
assert (X18 : getr (ms_regs ms) 18 = getr regs1 18) by mi_req HS0 HS.
assert (X23 : getr (ms_regs ms) 23 = getr regs1 23) by mi_req HS0 HS.
assert (X24 : getr (ms_regs ms) 24 = getr regs1 24) by mi_req HS0 HS.
assert (X19 : getr (ms_regs ms) 19 = getr regs1 19) by mi_req HS0 HS.
assert (X22 : getr (ms_regs ms) 22 = getr regs1 22) by mi_req HS0 HS.
assert (X25 : getr (ms_regs ms) 25 = getr regs1 25) by mi_req HS0 HS.
assert (X27 : getr (ms_regs ms) 27 = getr regs1 27) by mi_req HS0 HS.
pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA X2 X3 X4 X8 X9 X18 X23 X24 X19 X22 X25) as RAc.
(* the registers the run set *)
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20.
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite X2; exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite X3; exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite X4; exact R4).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite X8; exact R8).
assert (Q10' : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)) by (rewrite Q10, E52; reflexivity).
assert (Q11' : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)) by (rewrite Q11, (EE 26%nat 26%bv eq_refl); exact R26).
assert (Q12' : getr (ms_regs ms) 12 = w64 (frame_addr lyc 1 pos + 32))
  by (rewrite Q12, E34, unsigned_lit_small by lia; reflexivity).
assert (Q13' : getr (ms_regs ms) 13 = w64 24) by (rewrite Q13; reflexivity).
assert (Q20' : getr (ms_regs ms) 20 = w64 (frame_addr lyc 1 pos + 32))
  by (rewrite Q20, E34, unsigned_lit_small by lia; reflexivity).
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + MK_FRET)) by (rewrite Q1; reflexivity).
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
destruct (mi_slice_facts v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
  ltac:(lia)) as (SB & SR & SL & SA & SH & S0).
rewrite KV4 in SB, SR, SL.
refine (mf_fold_call B FOLD (mf_chain B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc (Some gi) line p rest
  (mf_next p rest) MK_FRET
  (p + Z.of_nat ov) (Z.of_nat vl) 24 (seg_spec.zb vv) CX LS CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1' _ _
  Q10' Q11' Q12' Q13' ltac:(lia) S0 SB SL SA SH _).
- unfold MK_FRET, AF_m_file; lia.
- unfold MK_FRET, AF_m_file; reflexivity.
- (* fold's return, 0x86870, at the same FP state: MK_FRET *)
  intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 LOW2 K2.
  rewrite (mi_fold_out vv SR) in A02, LOW2.
  pose proof (mf_regs_keep B v lyc pos (ms_regs ms) regs2 RAc HP2) as RA2.
  assert (R27' : getr regs2 27 = w64 (line + 1)).
  { rewrite <- R27, <- X27. exact (HP2 27 ltac:(unfold acallee_saved; lia)). }
  assert (R20' : getr regs2 20 = w64 (frame_addr lyc 1 pos + 32)).
  { rewrite <- Q20'. exact (HP2 20 ltac:(unfold acallee_saved; lia)). }
  exact (FRET v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest vv
    (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj LEN (conj NE (conj LOOP2
      (conj NP2 R27'))))))))))
    FIN' NZ SR (mi_zs_of_bytes _ _ _ (mi_hfold_rng vv SR) LOW2) A02 R20').
Qed.

(* MK_IRET 0x86854: the `beqz` on ieq's answer; KIGN (mi_ign) or the fold call to MK_FRET (mi_fold) *)
Lemma mk_iret_ok : forall n, MF_KIGN_stmt B n -> MK_FRET_stmt B n -> MK_IRET_stmt B n.
Proof.
intros n KIGN FRET. unfold MK_IRET_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KB KV MISS FIN S208 R21 S192 R26 A0.
destruct KB as (CX & LS & FRM & CORE & CELLS & RA & LEN & NE & LOOP & NP & R27).
destruct (ieq k S_model) eqn:HM; cbn [seg_spec.b2z] in A0.
- exact (mi_fold n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv FRET CX LS FRM CORE CELLS RA
    LEN NE LOOP KV MISS HM FIN S192 R26 R27 NP A0).
- exact (mi_ign n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KIGN CX LS FRM CORE CELLS RA
    LEN NE LOOP KV MISS HM FIN S208 R21 S192 R26 R27 NP A0).
Qed.
End e.
End f.
End d.

About mk_iret_ok.
Print Assumptions mk_iret_ok.
