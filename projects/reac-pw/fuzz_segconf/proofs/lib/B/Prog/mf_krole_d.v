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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 268 of its 327 lines of code are new or changed and 394 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KROLE: its first piece, from
   the cut KDISP 0x86714 (lib/B/Prog/m_file_m.v MF_KDISP_stmt) to KMODEL 0x86840 ("role" missed) or KR_FOLD 0x86728
   (lib/B/Prog/mf_krole_m.v KR_FOLD_stmt). A sub-lane of a walk lane of the image-B m_file-family owner's G2B. proves no function (kind:
   segment lemma of m_file's image-B walk, S_MF_KROLE piece kr_s_disp).
   Adapted from image A's lib/A/Prog/m_file_s_krole_d.v (kd_ret, kr_s_disp) and m_file_s_kign_1.v (ki_slice_facts,
   the seed with its regions dropped, the call of ieq and the `beqz` on its answer), a working branch

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 375-379):
     86714 auipc a1 / 86718 addi a2,a1      a2 = 0x21120 "role" (listing object 17, A_OBJ 17)
     8671c mv a1,s5                         a1 = kl (a0 = k = p + ok from 0x866e0: the cut's ka0 = true)
     86720 jal ieq                          a0 = b2z (ieq k "role") (m_file_iq.v mf_ieq_call), back at 0x86724
     86724 beqz a0,86840                    0: KMODEL with "role" missed; 1: KR_FOLD 0x86728
   No instruction reads or writes memory: each run starts from m_file_sd.v's seed with its regions dropped
   (st_ok_pi_submem), so the memory at each stop is the run's start memory (m_file_k.v mf_keep_run0 carries the cut
   facts). Image B has no min(vl, 63) and no vl = 0 test here (fold does both): the cut's registers s5 = kl, s10 = vl,
   s11 = line + 1 and the cell 192(s1) = v go to KR_FOLD as they are. No UBSan trap branch and no instrumented check
   in this code. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_krole_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* 0x86724, ieq's return point: the `beqz` (listing offset AF_m_file + 0x5e4) *)
Definition KD_RET : Z := AF_m_file + 0x5e4.

(* the words missed at KMODEL: "role" *)
Lemma kd_missed : forall k, ieq k S_role = false -> Forall (fun w => ieq k w = false) [S_role].
Proof. intros k H. constructor; [exact H | constructor]. Qed.

(* the line is a prefix of the text left (A's m_file_s_kign_t.v ki_line_le) *)
Lemma kd_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.

(* ieq_pre's bytes: the list Z read at a through an ASan reader, as list byte, and back (A's ki_bytes_of_zs) *)
Lemma kd_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (sa_aview_rng segs H mem _ _ (HZ i Hi)). }
split; [|exact (sa_zs_zb l HR)].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (A's ki_st_reg) *)
Lemma kd_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

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
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the text left's sub-range [o, o + n): its bytes as list byte, addressable, in the text block (A's
   m_file_s_kign_1.v ki_slice_facts) *)
Lemma kd_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (kd_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED (A's ki_pres) *)
Lemma kd_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
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

(* the seed at a K cut's pc with its regions dropped (a run that touches no memory); cur and np are not read *)
Lemma kd_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc pc,
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

(* an 8-byte frame cell off(s1) is kept by a change outside a window [lo, hi) below s1 *)
Lemma kd_slot_keep : forall v (W W' : world SEGS) m m' lo hi off x,
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

(* 0x86724, ieq's return: a0 = b2z (ieq k "role"); the `beqz` to KMODEL (0) or KR_FOLD (1), every other register
   and every byte the cut's *)
Lemma kd_ret : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MF_KMODEL_F B n -> KR_FOLD_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_slot v memc Wc 208 (p + Z.of_nat ok) -> getr regs1 21 = w64 (Z.of_nat kl) ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) -> getr regs1 26 = w64 (Z.of_nat vl) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (seg_spec.b2z (ieq k S_role)) ->
mf_at B v Wc regs1 memc mdc KD_RET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KMOD FOLD CX LS FRM CORE CELLS RA LEN NE
  LOOP KV FIN S208 R21 S192 R26 R27 NP A0.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (kd_seed0 v lyc Sc Wc regs1 memc mdc pos mcc KD_RET CX CORE RA) as HS1.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
destruct (ieq k S_role) eqn:HIE; cbn [seg_spec.b2z] in A0.
- (* "role": a0 = 1, the beqz falls through to KR_FOLD *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_FOLD.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (kd_pres E _ regs1 v lyc pos None 0 [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KR_FOLD by (unfold KR_FOLD, AF_m_file; reflexivity) end.
  apply (FOLD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv).
  + unfold kr_cx.
    exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj LEN (conj NE (conj (LPk mcc (Some gi) line p rest LOOP)
      (conj KV (conj FIN (conj (NPk _ NP) HIE))))))))))).
  + exact (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc).
  + exact (kd_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 192 _ CX (Z.le_refl _)
      ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S192).
  + transitivity (getr regs1 21); [exact (HPc 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  + transitivity (getr regs1 26); [exact (HPc 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  + transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
- (* "role" missed: a0 = 0, the beqz goes to KMODEL with the cut's state *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KMODEL.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (kd_pres E _ regs1 v lyc pos None 0 [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with MF_KMODEL by (unfold MF_KMODEL, AF_m_file; reflexivity) end.
  apply (KMOD fx v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE' CELLS'
    (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) LEN NE (LPk mcc (Some gi) line p rest LOOP) KV
    (kd_missed k HIE) FIN).
  + exact (kd_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX (Z.le_refl _)
      ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S208).
  + intros Hf. discriminate Hf.
  + transitivity (getr regs1 21); [exact (HPc 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  + exact (kd_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 192 _ CX (Z.le_refl _)
      ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S192).
  + transitivity (getr regs1 26); [exact (HPc 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  + transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  + exact (NPk _ NP).
Qed.

(* KDISP 0x86714: a2 = "role", a1 = kl, a0 = k; ieq(k, kl, "role") (m_file_iq.v mf_ieq_call), then kd_ret *)
Lemma kr_s_disp : forall n, MF_KMODEL_F B n -> KR_FOLD_stmt B n -> MF_KDISP_stmt B n.
Proof.
intros n KMOD FOLD. unfold MF_KDISP_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA LEN NE LOOP KV MISS FIN S208 R10 R21 S192 R26 R27 NP.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (kd_line_le rest) as Hml.
pose proof (kd_seed0 v lyc Sc Wc regs1 memc mdc pos mcc MF_KDISP CX CORE RA) as HS.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
(* 0x86714-0x86720: a2 = "role", a1 = kl; the jal to ieq *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (kd_pres E _ regs1 v lyc pos None 0 [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
(* the registers at the jal: the callee-saved ones are the cut's, a0 = k, a1 = kl, a2 = "role", ra = KD_RET *)
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (kd_st_reg SEGS _ _ _ _ 10%bv 10%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 10 (Z_to_bv 5 10) eq_refl). exact (R10 eq_refl). }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (kd_st_reg SEGS _ _ _ _ 11%bv 21%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_role)).
{ rewrite (kd_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 17) HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos None 0 [] (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_role 17 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KD_RET)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KD_RET HEI). }
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (NPk _ NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
pose proof (kd_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S208) as S208'.
pose proof (kd_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 192 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S192) as S192'.
destruct (kd_slice_facts v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
refine (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq
  pos MF_LOW_ON mcc (Some gi) line p rest (mf_next p rest) KD_RET (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k)
  S_role CX LS CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold KD_RET, AF_m_file; lia.
- unfold KD_RET, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  apply (kd_ret n v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv KMOD FOLD CX LS2 FRM CORE2
    CELLS2 (mf_regs_keep B v lyc pos regs1 regs2 RA HP12) LEN NE LOOP2 KV FIN).
  + exact (kd_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 208 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S208').
  + transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  + exact (kd_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 192 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S192').
  + transitivity (getr regs1 26); [exact (HP12 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  + transitivity (getr regs1 27); [exact (HP12 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  + exact NP2.
  + exact A02.
Qed.
End e.
End f.
End d.

About kr_s_disp.
Print Assumptions kr_s_disp.
