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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 394 of its 444 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB: the cut RFIND
   (0x865cc, m_find returned), i.e. the test of m_find's result and the whole FOUND arm, to the next cuts. A walk lane of the image-B m_file-family owner's G2B (a piece agent). proves no function (kind: segment lemma of m_file's image-B
   walk).
     hb9_rfind : MFB_JOIN_F n -> MFB_RREF1_F n -> MFB_NFIND_F n -> MFB_RFIND_F n          (mf_hdrb_2.v)
   WHAT THE CODE DOES (the neutral listing of m_file in image B, line = (pc - 0x86140) / 4 + 2, lines 293-312):
     0x865cc `beqz a0, 0x86b04`: a0 = m_find_ptr c mcc nm (m_find_c.v).
     NOT FOUND (SegModel.m_find mcc nm = None, a0 = 0): the branch is taken, to NFIND 0x86b04 with every register
       and every byte as they were (hb9_none_at; the seed run with a0 pinned to 0).
     FOUND (m_find mcc nm = Some i, a0 = g = &c->seg[i] = c + 256 i, i < |seg| by m_file_mdl.v's m_find_lt):
       0x865d0 `andi a1,a0,3`, 0x865d4 `bnez a1` to the `unimp` 0x86e84 (the UBSan alignment trap of g->gen): a0 is
         the seed's atom 52 = g with the fact HPTR 4 (g mod 16 = 0, from c mod 16 = 0, m_file_pre), so the token
         executor computes a1 = 0 and does not take the branch;
       0x865d8 `mv s5,a0`; 0x865dc a0 = g + 252; the instrumented check of the 4-byte load of g->gen (a load of the
         shadow byte at ((g + 252) >> 3) + the shadow base and a compare, 0x865e8 / 0x865ec; the slow path
         0x86d24-0x86d30 and the error path 0x86f30, a call of errpath_load4, are not reached): decided by the
         shadow entry mkSHE 52 0 260 (mf_she_at: [g, g + 260) addressable inside the block, i <= 31);
       0x865f0 `ld a1,104(s1)`, 0x865f4 `lb a1,0(a1)`: the instrumented check of c->gen (the shadow byte address
         (c + 0x23b0 >> 3) + the shadow base kept in 104(s1)); 0x865fc `bnez a1` to the slow path 0x86d34-0x86d44 and
         the error path 0x86f34-0x86f38, not reached: decided by the shadow entry mkSHE 33 0 9144 (mf_she_blk);
       0x865f8 `lw a0,0(a0)` (g->gen: the region of atom 52 [252, 256), its chunk atom 53 = ms_gen of entry i,
         mf_hdrb_1.v's hb_rd_seg_gen); 0x86600 `ld a1,56(s1)`, 0x86604 `lw a1,0(a1)` (c->gen: the region of atom 33
         [0x23b0, 0x23b4), its chunk atom 54 = mc_gen mcc, hb_rd_gen);
       0x86608 `bne a0,a1, 0x86ba0`: the two sign-extended 32-bit loads are equal exactly when the gens are
         (hb9_sext_U).
         other gen: to the join 0x86ba0 = MFB_JOIN (model by hb_mh_find_ne, hb_mod by hb4_mod_head_of);
         same gen: 0x8660c a0 = s9 = c, 0x86610 a1 = s11 = line + 1, 0x86614 `jal m_refuse` (m_file_rf.v's
           mf_refuse_step at listing offset AF_m_file + 0x4d4), back at 0x86618 = MFB_RREF1 (model by hb_mh_find_eq,
           hb_mod by hb4_mod_refuse; s4, s5 = g, s11 are callee-saved).
   No instruction of this piece writes memory: every region of its symbolic state is read-only (the seed's slot
   region set to an empty window), so each run keeps every byte (kept_of_frame) and m_file_k.v's mf_keep_run0
   carries every cut fact.
   Section hypotheses: VOBJS (the seed), SIGP, SSP, RELRO, M_REFUSE (mf_refuse_step), the texts of the HDRB piece plan. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m
  m_file_mdl m_file_sd m_file_k m_file_rf mf_hdrb_1 mf_hdrb_2 mf_hdrb_3 mf_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the `jal m_refuse` of the found path: 0x86614 (listing offset = AF_m_file + (pc - 0x86140)) *)
Definition HB9_JREF1 : Z := AF_m_file + 0x4d4.

(* the low word of a sign-extended 32-bit value (image A's m_file_s_hdrb_5.v hb5_sext32_low) *)
Lemma hb9_sext32_low : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 (x mod 2 ^ 32))) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* `lw` of a 4-byte chunk holding x (an atom), read back modulo 2 ^ 32: x *)
Lemma hb9_sext_U : forall E (n : nat) x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
  U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = x.
Proof.
intros E n x Hn Hx. rewrite U_SExt, (U_atom E n x Hn ltac:(lia)). change (Z.of_N 32) with 32.
apply hb9_sext32_low. exact Hx.
Qed.
(* a symbolic value that is an atom denotes the atom's word *)
Lemma hb9_denot_atom : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section i.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* ===================================== where the objects lie ===================================== *)
(* the block c below the allocator's ceiling, 16-aligned and apart from the side-stack frame; the stack above *)
Lemma hb9_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ mv_c v mod 16 = 0 /\
alloc_ceiling + 8592 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
(mf_s1 (mv_sp v) = mv_sp v - 320 \/ mf_s1 (mv_sp v) = mv_sp v - 336) /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
(mv_c v + seg_spec.SEG_M_SIZE <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= mv_c v).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mbc 1 pos HAR Hbc Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
change (fs_frame_bytes 1) with 128 in HFceil, Hsep.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & Hc16 & _).
destruct (mf_s1_facts B v CX) as (S1 & S2 & S3). destruct (mf_sp0 B v CX) as (P1 & P2 & P3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S3, P1.
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_M_SIZE in *.
repeat split; try lia.
Qed.

(* the five base atoms of the seed *)
Lemma hb9_bases : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_base v regs1 ->
bv_unsigned (ew (mfE regs1 v lyc pos cur np xs) 2) = mf_s1 (mv_sp v) /\
bv_unsigned (ew (mfE regs1 v lyc pos cur np xs) 8) = mv_sp v /\
bv_unsigned (ew (mfE regs1 v lyc pos cur np xs) 33) = mv_c v /\
bv_unsigned (ew (mfE regs1 v lyc pos cur np xs) 34) = frame_addr lyc 1 pos /\
bv_unsigned (ew (mfE regs1 v lyc pos cur np xs) 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs CX CORE RB.
destruct (hb9_geo v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof RB as (R2 & R8 & R9 & R18).
pose proof (mfE_extra regs1 v lyc pos cur np xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos cur np xs 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur np xs 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E33, E34, E36.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold seg_spec.SEG_M_SIZE in *.
split; [|split; [|split; [|split]]].
- rewrite (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), R2. apply mf_w64_u. lia.
- rewrite (mfE_reg regs1 v lyc pos cur np xs 8 8%bv eq_refl), R8. apply mf_w64_u. lia.
- rewrite E33. apply unsigned_lit_small. lia.
- rewrite E34. apply unsigned_lit_small. lia.
- rewrite E36. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
Qed.

(* the block's bytes are all below the shadow span or all above it *)
Lemma hb9_blk_sh : forall v, mf_cx B v ->
mv_c v + seg_spec.SEG_M_SIZE <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= mv_c v.
Proof.
intros v CX.
pose proof (mf_blk_app B v CX (mv_c v) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as A0.
pose proof (mf_blk_app B v CX (mv_c v + seg_spec.SEG_M_SIZE - 1) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as A1.
unfold seg_spec.SEG_M_SIZE, SHADOW_OFF in *. lia.
Qed.

(* the tactics of the walk (image A's m_file_s_hdrb.v) *)
Ltac hb9_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.
(* a register the run did not change: the same symbolic value before and after *)
Ltac hb9_same HS0 HS r :=
lazymatch type of HS0 with st_ok_pi _ _ ?E0 ?ss0 (restrict ?H0 ?ms0) =>
  let A := fresh "A" in let B' := fresh "B" in
  hb9_reg HS0 r A; hb9_reg HS r B'; rewrite B'; rewrite <- A; reflexivity
end.
Ltac hb9_norm HS := lazymatch type of HS with
| st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
Ltac hb9_awr_norm := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
Ltac hb9_awr_ro := repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a run whose regions are all read-only changed no byte *)
Ltac hb9_kept0 K := lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m1 a = aview SEGS H m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia | ]); destruct Hin
  | ] end.
Ltac hb9_pc pc := lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  let Hk := fresh in assert (Hk : k = pc) by (vm_compute; reflexivity); rewrite Hk; clear Hk end.

Section j.
Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ============================ NOT FOUND: 0x865cc `beqz a0` taken, to NFIND ============================
   the seed at MFB_RFIND with no extra value, the slot region read-only, a0 pinned to 0 *)
Lemma hb9_none_at : forall n, MFB_NFIND_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm -> m_find mcc nm = None ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 10 = w64 0 ->
mf_slot v memc Wc 192 (p + Z.of_nat o) -> getr regs1 26 = w64 (Z.of_nat (length nm)) ->
getr regs1 20 = w64 511 -> getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RFIND.
Proof.
intros n NFIND v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA Hlen Hne LOOP
  HNM Hf HFIN R10 SLOT R26 R20 R27 NP.
unfold mf_at.
pose proof CORE as (HJ & _).
pose proof LOOP as (_ & _ & _ & _ & _ & Lcur & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
destruct (hb9_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MFB_RFIND
  true true [] false false [] false CX CORE RB (fun _ => CELLS) HCUR (fun _ => NP) HNP ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
clearbody E.
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
clear HS.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 R10 eq_refl) as HS. clear HS1.
hb9_norm HS.
pose proof HS as HS0.
(* the run: 0x865cc `beqz a0` with a0 = 0, taken, to 0x86b04 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MFB_NFIND.
{ hb9_awr_norm. hb9_awr_ro. }
hb9_kept0 K.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 CX CORE CELLS HJ K)
  as (CORE2 & CELLS2 & NPK & LOOPK).
assert (SLOT2 : mf_slot v (ms_mem ms2) Wc 192 (p + Z.of_nat o)).
{ unfold mf_slot in *. apply (mf_val_keep Wc Wc memc (ms_mem ms2) (fun _ => False) _ 8 _ (fun a Ha _ => K a Ha));
    [lia | change (Z.of_nat 8) with 8; lia | intros k _ [] | exact SLOT]. }
assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb9_same HS0 HS (2%bv : bv 5)).
assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb9_same HS0 HS (3%bv : bv 5)).
assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb9_same HS0 HS (4%bv : bv 5)).
assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb9_same HS0 HS (8%bv : bv 5)).
assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb9_same HS0 HS (9%bv : bv 5)).
assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb9_same HS0 HS (18%bv : bv 5)).
assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb9_same HS0 HS (19%bv : bv 5)).
assert (Q20 : getr (ms_regs ms2) 20 = getr regs1 20) by (hb9_same HS0 HS (20%bv : bv 5)).
assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb9_same HS0 HS (22%bv : bv 5)).
assert (Q23 : getr (ms_regs ms2) 23 = getr regs1 23) by (hb9_same HS0 HS (23%bv : bv 5)).
assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb9_same HS0 HS (24%bv : bv 5)).
assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb9_same HS0 HS (25%bv : bv 5)).
assert (Q26 : getr (ms_regs ms2) 26 = getr regs1 26) by (hb9_same HS0 HS (26%bv : bv 5)).
assert (Q27 : getr (ms_regs ms2) 27 = getr regs1 27) by (hb9_same HS0 HS (27%bv : bv 5)).
pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25) as RA2.
pmkst HS. hb9_pc MFB_NFIND.
exact (NFIND v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos mcc cur line p rest o nm CX LS FRM CORE2 CELLS2 RA2
  Hlen Hne (LOOPK _ _ _ _ _ LOOP) HNM Hf HFIN SLOT2 ltac:(rewrite Q26; exact R26) ltac:(rewrite Q20; exact R20)
  ltac:(rewrite Q27; exact R27) (NPK _ NP)).
Qed.

(* ================================ FOUND: 0x865cc .. 0x86608, then JOIN or m_refuse ================================
   the seed at MFB_RFIND with xs = [g; g->gen; c->gen] (atoms 52, 53, 54), the slot region read-only, a0 pinned
   to atom 52 (fact HPTR 4), the regions of g->gen (atom 52, [252, 256)) and c->gen (atom 33, [0x23b0, 0x23b4)),
   the shadow entries of the block up to c->gen's granule and of [g, g + 260) *)
Lemma hb9_found_at : forall n, MFB_JOIN_stmt B n -> MFB_RREF1_F B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (nm : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
m_find mcc nm = Some i ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 10 = w64 (seg_spec.mseg_addr (mv_c v) i) ->
getr regs1 20 = w64 511 -> getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RFIND.
Proof.
intros n JOIN RREF1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest nm i CX LS FRM CORE CELLS RA Hlen Hne LOOP
  Hf HFIN R10 R20 R27 NP.
unfold mf_at.
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
destruct (hb_mconf_bounds _ _ _ HMC) as (Bseg & Bkept & Bgen & Bref & Bov & Bsg).
pose proof LOOP as (_ & _ & _ & _ & _ & Lcur & Lk0 & _).
pose proof (m_find_lt _ _ _ Hf) as Hi.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
destruct (hb9_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof (hb9_blk_sh v CX) as HBS.
unfold seg_spec.SEG_M_SIZE in G2, G10, HBS.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
set (g := seg_spec.mseg_addr (mv_c v) i).
assert (Hg : g = mv_c v + 256 * Z.of_nat i) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
set (gg := ms_gen (nth i (mc_seg mcc) mseg_d)).
pose proof (Bsg i Hi) as Bgg. fold gg in Bgg.
set (xs := [g; gg; mc_gen mcc]).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs MFB_RFIND
  true true [] false false [] false CX CORE RB (fun _ => CELLS) HCUR (fun _ => NP) HNP ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs 9144 CX CORE
  ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as SH33.
destruct (hb9_bases v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs CX CORE RB)
  as (B2 & B8 & B33 & B34 & B36).
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E52.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E53.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 2 ltac:(unfold A_TEXT; lia)) as E54.
cbn [Nat.add nth xs] in E52, E53, E54.
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (mfE regs1 v lyc pos cur (mf_next p rest) xs) k = getr regs1 r) by (intros; apply mfE_reg; assumption).
pose proof (mfE_U32 regs1 v lyc pos cur (mf_next p rest) xs) as U32.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) xs) in HS, SH33, B2, B8, B33, B34, B36, E52, E53, E54, ER, U32.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (B52 : bv_unsigned (ew E 52) = g) by (rewrite E52; apply unsigned_lit_small; lia).
(* the shadow entry of [g, g + 260): inside the block (i <= 31) *)
assert (SHG : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE 52 0 260)).
{ apply (mf_she_at E Wc memc 52 g 260 U32 E52 ltac:(lia) ltac:(lia)).
  - destruct (mf_addr_sub _ (mv_c v) seg_spec.SEG_M_SIZE g 260 HMA ltac:(lia)
      ltac:(unfold seg_spec.SEG_M_SIZE; lia) ltac:(lia)) as (_ & _ & _ & HRA & _).
    exact HRA.
  - intros x Hx. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9144; mkSHE 52 0 260] E (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_cons; [exact SH33 | apply Forall_cons; [exact SHG | apply Forall_nil]]).
clearbody E. clear SH33 SHG.
(* the slot region read-only *)
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
clear HS.
(* a0 = atom 52 = g *)
assert (D10 : sv_denot E (SOff 52 0) = getr regs1 10) by (rewrite (hb9_denot_atom E 52 _ E52), R10; reflexivity).
pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 52 0) HS1 eq_refl D10) as HS2. clear HS1.
hb9_norm HS2.
(* c->gen: atom 33, [0x23b0, 0x23b4), read-only, its chunk atom 54 *)
set (r33 := YP09.mkRegion (Some 33%nat) 0x23b0 0x23b4 0 0 [YP09.mkChunk 0x23b0 (CVal 4 (SOff 54 0))]).
assert (R33 : region_ok SEGS E (mrestrict (w_H Wc) memc) r33).
{ unfold region_ok, r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_c v) 0x23b0 4 (SOff 54 0) (mc_gen mcc)).
  - apply hb9_denot_atom. exact E54.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H Wc) memc (mv_c v + 0x23b0) (mc_gen mcc) (hb_rd_gen _ _ _ HMC)). }
assert (D33 : all_disjoint E r33 (ss_mem (ltac:(lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, r33.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ r33 HS2 ltac:(vm_compute; reflexivity) R33 D33) as HS3. clear HS2 R33 D33.
hb9_norm HS3.
(* g->gen: atom 52, [252, 256), read-only, its chunk atom 53 *)
set (rG := YP09.mkRegion (Some 52%nat) 252 256 0 0 [YP09.mkChunk 252 (CVal 4 (SOff 53 0))]).
assert (RG : region_ok SEGS E (mrestrict (w_H Wc) memc) rG).
{ unfold region_ok, rG. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B52.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ g 252 4 (SOff 53 0) gg).
  - apply hb9_denot_atom. exact E53.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H Wc) memc (g + 252) gg (hb_rd_seg_gen _ _ _ i HMC Hi)). }
assert (DG : all_disjoint E rG (ss_mem (ltac:(lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rG.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36, ?B52.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ rG HS3 ltac:(vm_compute; reflexivity) RG DG) as HS4. clear HS3 RG DG.
(* the fact on atom 52: g is 16-aligned *)
assert (F52 : afact_ok E 52 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite B52. split; [lia|]. split; [|lia].
  change (2 ^ 4) with 16. rewrite Hg. pose proof (Z.div_mod (mv_c v) 16 ltac:(lia)) as D16.
  replace (mv_c v + 256 * Z.of_nat i) with ((mv_c v / 16 + 16 * Z.of_nat i) * 16) by lia. apply Z_mod_mult. }
pose proof (st_ok_pi_add_fact E _ _ 52 (HPTR 4) HS4 F52) as HS. clear HS4.
hb9_norm HS.
pose proof HS as HS0.
(* run 1: 0x865cc .. 0x86608 (`beqz` not taken, the trap 0x865d4 not taken, the two checks, the two loads),
   stopped at `bne a0,a1` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ hb9_awr_norm. hb9_awr_ro. }
hb9_kept0 K1.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
(* 0x86608 `bne a0,a1`: a0 = the sign-extended g->gen, a1 = the sign-extended c->gen *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: the gens differ, to the join *)
  assert (Hgne : gg <> mc_gen mcc).
  { intros Heq. rewrite branch_ne_U in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc. apply Hc.
    rewrite !U_SExt, (U_atom E 53 gg E53 ltac:(lia)), (U_atom E 54 (mc_gen mcc) E54 ltac:(lia)), Heq. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MFB_JOIN.
  { hb9_awr_norm. hb9_awr_ro. }
  hb9_kept0 K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 CX CORE CELLS HJ K)
    as (CORE2 & CELLS2 & NPK & LOOPK).
  hb9_reg HS (21%bv : bv 5) Q21. rewrite (hb9_denot_atom E 52 _ E52) in Q21.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb9_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb9_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb9_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb9_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb9_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb9_same HS0 HS (18%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb9_same HS0 HS (19%bv : bv 5)).
  assert (Q20 : getr (ms_regs ms2) 20 = getr regs1 20) by (hb9_same HS0 HS (20%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb9_same HS0 HS (22%bv : bv 5)).
  assert (Q23 : getr (ms_regs ms2) 23 = getr regs1 23) by (hb9_same HS0 HS (23%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb9_same HS0 HS (24%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb9_same HS0 HS (25%bv : bv 5)).
  assert (Q27 : getr (ms_regs ms2) 27 = getr regs1 27) by (hb9_same HS0 HS (27%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25) as RA2.
  pose proof HFIN as HFIN'. rewrite (hb_mh_find_ne mcc nm (line + 1) i Hf Hgne) in HFIN'.
  pmkst HS. hb9_pc MFB_JOIN.
  exact (JOIN v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos mcc mcc cur line p rest i CX LS FRM CORE2 CELLS2 RA2
    Hlen Hne (LOOPK _ _ _ _ _ LOOP) (hb4_mod_head_of (mv_k0 v) mcc cur Lcur Lk0) Hi HFIN' Q21
    ltac:(rewrite Q20; exact R20) ltac:(rewrite Q27; exact R27) (NPK _ NP)).
- (* not taken: the gens are equal, m_refuse(c, line + 1) *)
  assert (Hgeq : gg = mc_gen mcc).
  { rewrite branch_ne_U in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    pose proof (hb9_sext_U E 53 gg E53 Bgg) as X. pose proof (hb9_sext_U E 54 (mc_gen mcc) E54 Bgen) as Y.
    rewrite Hc in X. rewrite X in Y. exact Y. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HB9_JREF1.
  { hb9_awr_norm. hb9_awr_ro. }
  hb9_kept0 K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 CX CORE CELLS HJ K)
    as (CORE2 & CELLS2 & NPK & LOOPK).
  (* the registers at the `jal`: a0 = s9 = c, a1 = s11 = line + 1, s5 = g *)
  hb9_reg HS (10%bv : bv 5) Q10. rewrite (hb9_denot_atom E 25 _ (ER 25%nat 25%bv eq_refl)), R25 in Q10.
  hb9_reg HS (11%bv : bv 5) Q11. rewrite (hb9_denot_atom E 27 _ (ER 27%nat 27%bv eq_refl)), R27 in Q11.
  hb9_reg HS (21%bv : bv 5) Q21. rewrite (hb9_denot_atom E 52 _ E52) in Q21.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb9_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb9_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb9_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb9_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb9_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb9_same HS0 HS (18%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb9_same HS0 HS (19%bv : bv 5)).
  assert (Q20 : getr (ms_regs ms2) 20 = getr regs1 20) by (hb9_same HS0 HS (20%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb9_same HS0 HS (22%bv : bv 5)).
  assert (Q23 : getr (ms_regs ms2) 23 = getr regs1 23) by (hb9_same HS0 HS (23%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb9_same HS0 HS (24%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb9_same HS0 HS (25%bv : bv 5)).
  assert (Q27 : getr (ms_regs ms2) 27 = getr regs1 27) by (hb9_same HS0 HS (27%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25) as RA2.
  pose proof RA2 as ((R2' & R3' & R4' & R8' & _) & _).
  (* the model: m_refuse, then g->gen = c->gen at the join *)
  pose proof (hb_mh_find_eq mcc nm (line + 1) i Hf Hgeq) as EM. cbv zeta in EM.
  pose proof HFIN as HFIN'. rewrite EM in HFIN'.
  destruct (hb_refuse_fields mcc (line + 1) false) as (Egen & Eov & Eref & Eseg & Erd).
  assert (Hi1 : (i < length (mc_seg (m_refuse mcc (line + 1) false)))%nat) by (rewrite Eseg; exact Hi).
  assert (HKEPT : (length (mc_kept (m_refuse mcc (line + 1) false)) <= length (mc_kept (mf_final v)))%nat).
  { pose proof (mf_kept_le_final (m_upd (m_refuse mcc (line + 1) false) i
      (ms_with_gen (mc_gen (m_refuse mcc (line + 1) false)))) (Some i) (line + 1) (lines (mf_rest rest))
      (mf_final v)) as HK.
    rewrite (proj2 (m_upd_sizes (m_refuse mcc (line + 1) false) i _)) in HK. apply HK; [|exact HFIN'].
    unfold mf_cur_ok. rewrite (proj1 (m_upd_sizes (m_refuse mcc (line + 1) false) i _)), upd_nth_length. exact Hi1. }
  pmkst HS. hb9_pc HB9_JREF1.
  apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos MF_LOW_OFF
    mcc mcc false cur line p rest (mf_next p rest) HB9_JREF1 CX LS FRM
    (mf_corek_of_core B v lyc Sc Wc (ms_mem ms2) md2 pos MF_LOW_OFF mcc CORE2) CELLS2 (NPK _ NP) R2' R3' R4' R8'
    (LOOPK _ _ _ _ _ LOOP) Hne eq_refl Lk0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Q10 Q11
    HKEPT).
  intros fx1 ly2 S2 W2 regs3 mem3 md3 HFX LS3 CORE3 CELLS3 NP3 LOOP3 HCS.
  assert (Ely : ly2 = lyc) by (destruct LS3 as (E1 & _); destruct LS as (E2 & _); congruence). subst ly2.
  replace (HB9_JREF1 + 4) with MFB_RREF1 by (vm_compute; reflexivity).
  assert (H20 : getr regs3 20 = getr (ms_regs ms2) 20) by exact (HCS 20 ltac:(unfold acallee_saved; lia)).
  assert (H21 : getr regs3 21 = getr (ms_regs ms2) 21) by exact (HCS 21 ltac:(unfold acallee_saved; lia)).
  assert (H27 : getr regs3 27 = getr (ms_regs ms2) 27) by exact (HCS 27 ltac:(unfold acallee_saved; lia)).
  exact (RREF1 fx1 v lyc S2 W2 regs3 mem3 md3 pos mcc (m_refuse mcc (line + 1) false) cur line p rest i CX LS3
    (fxrel_frm0 fx fx1 FRM HFX) CORE3 CELLS3 (mf_regs_at_kept B v lyc pos (ms_regs ms2) regs3 RA2 HCS) Hlen Hne LOOP3
    (hb4_mod_refuse (mv_k0 v) mcc mcc cur (line + 1) false (hb4_mod_head_of (mv_k0 v) mcc cur Lcur Lk0) eq_refl)
    Hi1 HFIN' ltac:(rewrite H21; exact Q21) ltac:(rewrite H20, Q20; exact R20) ltac:(rewrite H27, Q27; exact R27)
    NP3).
Qed.

(* ================================ RFIND 0x865cc: the case on m_find's result ================================ *)
Lemma hb9_rfind_at : forall n, MFB_JOIN_stmt B n -> MFB_RREF1_F B n -> MFB_NFIND_stmt B n -> MFB_RFIND_stmt B n.
Proof.
intros n JOIN RREF1 NFIND v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA Hlen Hne
  LOOP HNM HFIN R10 SLOT R26 R20 R27 NP.
unfold m_find_ptr in R10.
destruct (m_find mcc nm) as [i|] eqn:Hf.
- exact (hb9_found_at n JOIN RREF1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest nm i CX LS FRM CORE CELLS RA
    Hlen Hne LOOP Hf HFIN R10 R20 R27 NP).
- exact (hb9_none_at n NFIND v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA
    Hlen Hne LOOP HNM Hf HFIN R10 SLOT R26 R20 R27 NP).
Qed.
End j.

(* the piece at every FP state *)
Lemma hb9_rfind : forall n, MFB_JOIN_F B n -> MFB_RREF1_F B n -> MFB_NFIND_F B n -> MFB_RFIND_F B n.
Proof. intros n JOIN RREF1 NFIND fx0. exact (hb9_rfind_at (fx := fx0) n (JOIN fx0) RREF1 (NFIND fx0)). Qed.
End i.
End h.
End g.
About hb9_rfind.
Print Assumptions hb9_rfind.
