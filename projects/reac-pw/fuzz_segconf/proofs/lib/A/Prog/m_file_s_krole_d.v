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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 353 of its 403 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KROLE: its first piece, from the cut KDISP 0x86684
   (lib/A/Prog/m_file_m.v MF_KDISP_stmt) to KMODEL 0x867b8 ("role" missed), the fold's first pass KR_FOLD 0x866c0
   or the fold's end KR_POST 0x8672c (lib/A/Prog/m_file_s_krole_m.v). The KROLE dispatch sub-lane of the G2 walk owner's
   G2. proves no function (kind: segment lemma of m_file's walk, S_MF_KROLE piece kr_s_disp).

   THE CODE (listing m_file.fuzz_segconf.asan.s lines 500-514):
     86684 auipc a0 / 86688 addi a2,a0      a2 = 0x21120 "role" (listing object 17)
     8668c mv a0,s11 / 86690 mv a1,s6       a0 = k = p + ok, a1 = kl
     86694 jal ieq                          a0 = b2z (ieq k "role") (m_file_iq.v mf_ieq_call), back at 0x86698
     86698 beqz a0,867b8                    0: KMODEL, "role" added to the words missed
     8669c li a0,63 / 866a0 bltu s4,a0 / 866a4 li s4,63      s4 = kr_ln vl = min(vl, 63)
     866a8 ld a7,152(s1)                    a7 = low.i = FB + 32 (the spill slot mf_cells names)
     866ac beq s7,s5,8672c                  s7 = s5 exactly when vl = 0: KR_POST (low.i holds kr_low [] = [])
     866b0 mv a0,s5 / mv a2,a7 / mv a1,a7 / 866bc mv a3,s4   KR_FOLD with j = 0
   No instruction reads or writes memory except the slot load at 0x866a8 and the call: every run starts from
   m_file_sd.v's seed with every region read-only (the slot window closed), so the memory at each stop is the cut's
   (m_file_k.v mf_keep_run0 carries the cut facts). The two branches of the bltu and of the beq are split
   symbolically (psrr_branch_tok); the case vl >= 63 with vl = 0 is impossible. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kign_t m_file_s_kign_1 m_file_s_krole_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* 0x86698, ieq's return point (listing offset AF_m_file + 0x7dc) *)
Definition KD_RET : Z := AF_m_file + 0x7dc.
(* the piece's regions: m_file_sd.v's mf_regions (cells, np, low.i in scope) with the slot window closed *)
Definition kd_rs : smem :=
  list_upd (mf_regions true true [] false false [] false MF_LOW_ON) 1 (set_window (mf_r_slots true true []) 0 0).
Definition kd_ss (pc : Z) : sstate := mkSS pc sr_mf kd_rs None mf_facts.

(* the words missed at KMODEL: "role" *)
Lemma kd_missed : forall k, ieq k S_role = false -> Forall (fun w => ieq k w = false) [S_role].
Proof. intros k H. constructor; [exact H | constructor]. Qed.

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac kd_awr :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac kd_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* name the model after a run (fuzz_command check_reply_s2.v cr2_name_md) *)
Ltac kd_name_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => let m := fresh "mdq" in set (m := d) in *; clearbody m end.
(* after a run from a read-only state: its memory is the run's start memory, composed into KM (the memory at the
   segment's start) *)
Ltac kd_mem KM :=
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
Ltac kd_req HS0 HS :=
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
Ltac kd_regs_pres HS0 HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [-> | Hc]; [kd_req HS0 HS |]); subst r; kd_req HS0 HS.

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
(* the shared Section hypotheses (the KROLE segment lane's KROLE-PIECES.md section 2) this piece uses *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the piece's symbolic state at pc: mf_seed's (cells, np in 144(s1), low.i in scope, no extra atom) with the slot
   window closed (check_reply_s7.v cr7_seed's form) *)
Lemma kd_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi p rest pc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 -> mf_np v memc Wc (mf_next p rest) ->
0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64 -> 0 <= mf_next p rest < 2 ^ 64 ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) (kd_ss pc)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi p rest pc CX CORE CELLS RA NP HC HN.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] pc
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) HC (fun _ => NP)
  HN ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (st_ok_pi_region_nth _ _ _ 1 (mf_r_slots true true []) HS eq_refl) as Hr.
exact (ast_ok_pi_set_region _ _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity) (region_ok_rewindow SEGS _ _ _ 0 0 Hr ltac:(intros o Ho; lia))).
Qed.

(* KR_POST from the facts at 0x8672c when vl = 0 (low.i holds kr_low [] = []) *)
Lemma kd_post : forall n v lyc Sc Wc regs memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov : nat) (k vv : list Z),
KR_POST_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc ->
mf_cells v lyc pos memc Wc (Some gi) -> (length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mcc (Some gi) line p rest -> mk_kv rest ok kl ov 0 k vv ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v -> mf_np v memc Wc (mf_next p rest) ->
ieq k S_role = true -> mf_regs_at B v lyc pos regs ->
getr regs 20 = w64 0 -> getr regs 24 = w64 (line + 1) -> getr regs 17 = w64 (frame_addr lyc 1 pos + 32) ->
mf_at B v Wc regs memc mdc KR_POST.
Proof.
intros n v lyc Sc Wc regs memc mdc pos mcc gi line p rest ok kl ov k vv POST CX LS FRM CORE CELLS LEN NE LOOP KV FIN NP
  HIE RA R20 R24 R17.
assert (Evv : vv = []) by (destruct KV as (_ & _ & _ & Ev); rewrite <- Ev; reflexivity).
apply (POST v lyc Sc Wc regs memc mdc pos mcc gi line p rest ok kl ov 0%nat k vv
  (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj LEN (conj NE (conj LOOP (conj KV (conj FIN (conj NP HIE)))))))))))
  RA).
- subst vv. unfold kr_low_at. replace (kr_low []) with (@nil Z) by reflexivity. intros i Hi. cbn in Hi. lia.
- exact R20.
- exact R24.
- exact R17.
Qed.

(* KR_FOLD's first pass (j = 0) from the facts at 0x866c0 when vl > 0 *)
Lemma kd_fold : forall n v lyc Sc Wc regs memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
KR_FOLD_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc ->
mf_cells v lyc pos memc Wc (Some gi) -> (length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mcc (Some gi) line p rest -> mk_kv rest ok kl ov vl k vv ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v -> mf_np v memc Wc (mf_next p rest) ->
ieq k S_role = true -> mf_regs_at B v lyc pos regs -> (0 < vl)%nat ->
getr regs 20 = w64 (Z.of_nat (kr_ln vl)) -> getr regs 24 = w64 (line + 1) ->
getr regs 17 = w64 (frame_addr lyc 1 pos + 32) ->
getr regs 21 = w64 (p + Z.of_nat ov) -> getr regs 10 = w64 (p + Z.of_nat ov) ->
getr regs 11 = w64 (frame_addr lyc 1 pos + 32) -> getr regs 12 = w64 (frame_addr lyc 1 pos + 32) ->
getr regs 13 = w64 (Z.of_nat (kr_ln vl)) ->
mf_at B v Wc regs memc mdc KR_FOLD.
Proof.
intros n v lyc Sc Wc regs memc mdc pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM CORE CELLS LEN NE LOOP KV FIN
  NP HIE RA Hvl R20 R24 R17 R21 R10 R11 R12 R13.
apply (FOLD v lyc Sc Wc regs memc mdc pos mcc gi line p rest ok kl ov vl k vv 0%nat
  (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj LEN (conj NE (conj LOOP (conj KV (conj FIN (conj NP HIE)))))))))))
  RA).
- unfold kr_ln. lia.
- unfold kr_low_at. intros i Hi. exfalso. rewrite firstn_O in Hi. cbn [length] in Hi. lia.
- exact R20.
- exact R24.
- exact R17.
- rewrite Nat.add_0_r. exact R21.
- rewrite Nat.add_0_r. exact R10.
- cbn [Z.of_nat]. rewrite Z.add_0_r. exact R11.
- cbn [Z.of_nat]. rewrite Z.add_0_r. exact R12.
- rewrite Nat.sub_0_r. exact R13.
Qed.

(* 0x86698, ieq's return: a0 = b2z (ieq k "role"); 0 to KMODEL, 1 through s4 = min(vl, 63), a7 = low.i to KR_POST
   (vl = 0) or KR_FOLD (vl > 0) *)
Lemma kd_ret : forall n v lyc Sc Wc regs2 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MF_KMODEL_F B n -> KR_FOLD_stmt B n -> KR_POST_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs2 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs2 27 = w64 (p + Z.of_nat ok) -> getr regs2 22 = w64 (Z.of_nat kl) ->
getr regs2 21 = w64 (p + Z.of_nat ov) -> getr regs2 20 = w64 (Z.of_nat vl) ->
getr regs2 23 = w64 (p + Z.of_nat (ov + vl)) -> getr regs2 24 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
getr regs2 10 = w64 (seg_spec.b2z (ieq k S_role)) ->
mf_at B v Wc regs2 memc mdc KD_RET.
Proof.
intros n v lyc Sc Wc regs2 memc mdc pos mcc gi line p rest ok kl ov vl k vv KMOD FOLD POST CX LS FRM CORE CELLS RA LEN NE
  LOOP KV FIN R27 R22 R21 R20 R23 R24 NP R10.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & Hcur & _).
pose proof KV as (KV1 & KV2 & _ & _).
pose proof (ki_line_le rest) as Hml.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as HC.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as HN.
pose proof (kd_seed v lyc Sc Wc regs2 memc mdc pos mcc gi p rest KD_RET CX CORE CELLS RA NP HC HN) as HS.
remember (mfE regs2 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr regs2 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) [])
  (Z_to_bv 64 0)) by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. cbn [Nat.add nth mf_extra map app] in E34.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hfin) as (F1 & F2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U20 : U E (SOff 20 0) = Z.of_nat vl)
  by (apply (U_atom E 20 (Z.of_nat vl)); [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
assert (U21 : U E (SOff 21 0) = p + Z.of_nat ov)
  by (apply (U_atom E 21 (p + Z.of_nat ov)); [rewrite (EE 21%nat 21%bv eq_refl); exact R21 | lia]).
assert (U23 : U E (SOff 23 0) = p + Z.of_nat (ov + vl))
  by (apply (U_atom E 23 (p + Z.of_nat (ov + vl))); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]).
assert (U63 : U E (SLit 63) = 63) by reflexivity.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (KM : forall x, memc x = memc x) by reflexivity.
unfold mf_at.
assert (HB : ieq k S_role = true \/ ieq k S_role = false) by (destruct (ieq k S_role); auto).
destruct HB as [HIE | HIE]; rewrite HIE in R10; cbn [seg_spec.b2z] in R10.
- (* ieq k "role" = 1 *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS ltac:(exact R10) eq_refl) as HSp.
  kd_norm HSp. clear HS. rename HSp into HS. pose proof HS as HS0.
  (* 0x86698-0x866a0: the beqz falls through, a0 = 63; stop at the bltu *)
  paj_run_tok RUN HS HJ SHOK Bspan; [kd_awr|].
  kd_mem KM. kd_name_md.
  psrr_branch_tok RUN BR HS SHOK Bspan; rename Hc into Hlt; rewrite branch_ltu_U, U20, U63 in Hlt.
  + (* vl < 63: s4 stays vl *)
    apply Z.ltb_lt in Hlt.
    assert (Hln : kr_ln vl = vl) by (unfold kr_ln; lia).
    (* 0x866a8: a7 = low.i; stop at the beq *)
    paj_run_tok RUN HS HJ SHOK Bspan; [kd_awr|].
    kd_mem KM. kd_name_md.
    psrr_branch_tok RUN BR HS SHOK Bspan; rewrite branch_eq_U, U23, U21 in Hc.
    * (* vl = 0: KR_POST *)
      apply Z.eqb_eq in Hc. assert (Hv0 : vl = 0%nat) by lia. subst vl.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_POST; [kd_awr|].
      kd_mem KM. kd_name_md.
      prreg HS (17%bv : bv 5) Q17.
      assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
        by (apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RA); kd_req HS0 HS).
      assert (X20 : getr (ms_regs ms) 20 = getr regs2 20) by kd_req HS0 HS.
      assert (X24 : getr (ms_regs ms) 24 = getr regs2 24) by kd_req HS0 HS.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
        assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
          by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
        destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
          as (CORE' & CELLS' & NPk & LOOPk) end.
      apply (kd_post n v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc gi line p rest ok kl ov k vv POST CX LS FRM CORE'
        CELLS' LEN NE (LOOPk _ _ _ _ _ LOOP) KV FIN (NPk _ NP) HIE RA').
      -- rewrite X20. exact R20.
      -- rewrite X24. exact R24.
      -- rewrite Q17, E34, unsigned_lit_small by lia. reflexivity.
    * (* vl > 0: the fold's first pass *)
      apply Z.eqb_neq in Hc. assert (Hv0 : (0 < vl)%nat) by lia.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_FOLD; [kd_awr|].
      kd_mem KM. kd_name_md.
      prreg HS (17%bv : bv 5) Q17. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
      assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
        by (apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RA); kd_req HS0 HS).
      assert (X20 : getr (ms_regs ms) 20 = getr regs2 20) by kd_req HS0 HS.
      assert (X21 : getr (ms_regs ms) 21 = getr regs2 21) by kd_req HS0 HS.
      assert (X24 : getr (ms_regs ms) 24 = getr regs2 24) by kd_req HS0 HS.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
        assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
          by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
        destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
          as (CORE' & CELLS' & NPk & LOOPk) end.
      apply (kd_fold n v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM
        CORE' CELLS' LEN NE (LOOPk _ _ _ _ _ LOOP) KV FIN (NPk _ NP) HIE RA' Hv0).
      -- rewrite Hln, X20. exact R20.
      -- rewrite X24. exact R24.
      -- rewrite Q17, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite X21. exact R21.
      -- rewrite Q10, (EE 21%nat 21%bv eq_refl). exact R21.
      -- rewrite Q11, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite Q12, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite Hln, Q13, (EE 20%nat 20%bv eq_refl). exact R20.
  + (* vl >= 63: s4 = 63 *)
    apply Z.ltb_ge in Hlt.
    assert (Hln : kr_ln vl = 63%nat) by (unfold kr_ln; lia).
    paj_run_tok RUN HS HJ SHOK Bspan; [kd_awr|].
    kd_mem KM. kd_name_md.
    psrr_branch_tok RUN BR HS SHOK Bspan; rewrite branch_eq_U, U23, U21 in Hc.
    * (* vl = 0 contradicts vl >= 63 *)
      apply Z.eqb_eq in Hc. exfalso. lia.
    * apply Z.eqb_neq in Hc. assert (Hv0 : (0 < vl)%nat) by lia.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_FOLD; [kd_awr|].
      kd_mem KM. kd_name_md.
      prreg HS (17%bv : bv 5) Q17. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20.
      assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
        by (apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RA); kd_req HS0 HS).
      assert (X21 : getr (ms_regs ms) 21 = getr regs2 21) by kd_req HS0 HS.
      assert (X24 : getr (ms_regs ms) 24 = getr regs2 24) by kd_req HS0 HS.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
        assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
          by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
        destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
          as (CORE' & CELLS' & NPk & LOOPk) end.
      apply (kd_fold n v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM
        CORE' CELLS' LEN NE (LOOPk _ _ _ _ _ LOOP) KV FIN (NPk _ NP) HIE RA' Hv0).
      -- rewrite Hln, Q20. reflexivity.
      -- rewrite X24. exact R24.
      -- rewrite Q17, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite X21. exact R21.
      -- rewrite Q10, (EE 21%nat 21%bv eq_refl). exact R21.
      -- rewrite Q11, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite Q12, E34, unsigned_lit_small by lia. reflexivity.
      -- rewrite Hln, Q13. reflexivity.
- (* ieq k "role" = 0: the beqz is taken, to KMODEL with "role" missed *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS ltac:(exact R10) eq_refl) as HSp.
  kd_norm HSp. clear HS. rename HSp into HS. pose proof HS as HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KMODEL; [kd_awr|].
  kd_mem KM. kd_name_md.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
    by (apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RA); kd_req HS0 HS).
  assert (X27 : getr (ms_regs ms) 27 = getr regs2 27) by kd_req HS0 HS.
  assert (X22 : getr (ms_regs ms) 22 = getr regs2 22) by kd_req HS0 HS.
  assert (X21 : getr (ms_regs ms) 21 = getr regs2 21) by kd_req HS0 HS.
  assert (X20 : getr (ms_regs ms) 20 = getr regs2 20) by kd_req HS0 HS.
  assert (X23 : getr (ms_regs ms) 23 = getr regs2 23) by kd_req HS0 HS.
  assert (X24 : getr (ms_regs ms) 24 = getr regs2 24) by kd_req HS0 HS.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
      by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
    destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
      as (CORE' & CELLS' & NPk & LOOPk) end.
  apply (KMOD fx v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE' CELLS' RA'
    LEN NE (LOOPk _ _ _ _ _ LOOP) KV (kd_missed k HIE) FIN).
  + rewrite X27. exact R27.
  + rewrite X22. exact R22.
  + rewrite X21. exact R21.
  + rewrite X20. exact R20.
  + rewrite X23. exact R23.
  + rewrite X24. exact R24.
  + exact (NPk _ NP).
Qed.

(* KDISP 0x86684: ieq(k, kl, "role") (m_file_iq.v mf_ieq_call), then kd_ret *)
Lemma kr_s_disp : forall n, MF_KMODEL_F B n -> KR_FOLD_stmt B n -> KR_POST_stmt B n -> MF_KDISP_stmt B n.
Proof.
intros n KMOD FOLD POST. unfold MF_KDISP_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA LEN NE LOOP KV MISS FIN R27 R22 R21 R20 R23 R24 NP.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _).
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (ki_line_le rest) as Hml.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as HC.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as HN.
pose proof (kd_seed v lyc Sc Wc regs1 memc mdc pos mcc gi p rest MF_KDISP CX CORE CELLS RA NP HC HN) as HS.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (KM : forall x, memc x = memc x) by reflexivity.
pose proof CORE as (HJ & _).
pose proof HS as HS0.
unfold mf_at.
(* 0x86684-0x86694: a2 = "role", a0 = k, a1 = kl; stop at the jal *)
paj_run_tok RUN HS HJ SHOK Bspan; [kd_awr|].
kd_mem KM. kd_name_md.
assert (HPc : aregs_preserved regs1 (ms_regs ms)) by (kd_regs_pres HS0 HS).
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof RA as (R2 & R3 & R4 & R8 & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10' : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)) by (rewrite Q10, (EE 27%nat 27%bv eq_refl); exact R27).
assert (Q11' : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)) by (rewrite Q11, (EE 22%nat 22%bv eq_refl); exact R22).
assert (Q12' : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_role)).
{ rewrite Q12, (img_env_atomP E 258%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_role 17 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KD_RET)) by (rewrite Q1; reflexivity).
pmkst HS.
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?md) _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mm a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite KM; reflexivity);
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mm md CX CORE CELLS HJ K0)
    as (CORE' & CELLS' & NPk & LOOPk) end.
pose proof (NPk _ NP) as NP'. pose proof (LOOPk _ _ _ _ _ LOOP) as LOOP'.
destruct (ki_slice_facts B v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos MF_LOW_ON mcc (Some gi)
  line p rest (mf_next p rest) KD_RET (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) S_role CX LS CORE' CELLS' LOOP'
  NP' Q2 Q3 Q4 Q8 Q1' _ _ _ Q10' Q11' Q12' S0 SB SL SA SH _).
- unfold KD_RET, AF_m_file; lia.
- unfold KD_RET, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  apply (kd_ret n v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv KMOD FOLD POST CX LS2 FRM CORE2
    CELLS2 (mf_regs_keep B v lyc pos regs1 regs2 RA HP12) LEN NE LOOP2 KV FIN).
  + rewrite <- R27. exact (HP12 27 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R22. exact (HP12 22 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R21. exact (HP12 21 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R20. exact (HP12 20 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R23. exact (HP12 23 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R24. exact (HP12 24 ltac:(unfold acallee_saved; lia)).
  + exact NP2.
  + exact A02.
Qed.
End e.
End f.
End d.

About kr_s_disp.
Print Assumptions kr_s_disp.
