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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 371 of its 424 lines of code are new or changed and 400 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP: the
   hit path of the ignore value, KI_HIT 0x86a18 -> KI_SNR 0x86a78 (lib/B/Prog/mf_kignp_m.v). A walk lane of
   the image-B m_file-family owner's G2B (a piece agent).
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's hit-path piece ki_s_hit). ADAPTED from the
   image-B KROLE hit piece lib/B/Prog/mf_krole_h.v (commit 2cb3b888d466: kr_hit_run's
   seed / region / shadow-entry pattern and kr_s_hit's snprintf step and cut carry) at S_MF_KIGNP's stores and
   continuation.

   THE CODE (the neutral listing of m_file in image B lines 568-592, slow paths 742-749, error paths 888-889):
     0x86a18 a0 = 136(s1) = cur = &c->seg[gi]; 0x86a1c a0 = a0 & 3
     0x86a20 `bnez a0` -> unimp 0x86e84 (UBSan: alignment of cur)
     0x86a24 a3 = 136(s1) = g; 0x86a28-0x86a38 the check of g->ignore (store4 at g + 24; slow path 0x86cd0, error
       path 0x86f18); 0x86a3c g->ignore = s4 = b2z b
     0x86a40-0x86a54 the check of g->ignore_set (store4 at g + 28; slow path 0x86ce0, error path 0x86f1c), with
       0x86a50 s9 = 112(s1) = c between its load and its branch; 0x86a5c g->ignore_set = 1
     0x86a60-0x86a70 a0 = g + 156 (g->ignore_file), a2 = "%s" (listing object 14, 0x21080), a1 = 96,
       a3 = 64(s1) = &c->reading; 0x86a74 jal snprintf (ra = BASE + KI_SNR).
   THE TRAP EDGE (refuted at its branch, never stepped over):
     0x86a20 `bnez a0`, a0 = cur & 3: decided by the executor from the fact HPTR 4 of atom 37 (136(s1) = cur =
       mf_cur_ptr c (Some gi) = c + 256 gi, 16-aligned since c mod 16 = 0, mf_cx's m_file_pre); the taken edge
       (the `unimp` at 0x86e84) is never a successor of the run.
   THE CHECKS (each a load of the shadow byte at (a >> 3) + s2 and a compare; decided by the token executor from the
   shadow entry ki_h_SH = mkSHE 37 24 32, which holds since the mconf block [c, c + 9236) is addressable (mf_core's
   sa_addr) and g + 32 <= c + 7968; the slow paths are not entered, the error paths 0x86f18 / 0x86f1c are not
   reached):
     0x86a38 store4 at g + 24 and 0x86a54 store4 at g + 28.
   THE PROOF: ki_h_run, one seed (mf_kignp_c.v ki_seed, s9 pinned to atom 33) cut down to the frame cells made
   read-only, plus g's 8 bytes [24, 32) at atom 37 (written); one token run to the snprintf call. ki_s_hit joins it
   with snprintf's step (m_file_sn.v mf_snp_field_call, off = MS_IGNORE_FILE, ret = KI_SNR): the block then holds
   m_upd mcc gi (ms_with_ignore b (mc_reading mcc)) (mf_kignp_t.v ki_e_mconf_ign; ki_snp_reading turns the model's
   snprintf_s into c->reading), the cut facts are carried by m_file_k.v's mf_keep / mf_keep_cells / mf_loop_keep, and
   KI_SNR's statement (KI_DONE_stmt) is applied at the FP state snprintf returns, with mcl = mcc.
   Section hypotheses: VOBJS, SSP, RELRO, ASNPRINTF (SSP and RELRO because the shared step m_file_sn.v asks SSP and
   its KRODJ, which m_file_k.v's mf_rod_now_j gives from RELRO). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFCmd RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_mdl m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_sn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* c->reading as sa_mconf holds it: a C string of fewer than 96 bytes, its bytes and NUL at c + MC_READING *)
Lemma ki_h_reading : forall (rd : reader) c mc, sa_mconf rd c mc ->
  sa_zs rd (c + seg_spec.MC_READING) (mc_reading mc ++ [0]) /\ (length (mc_reading mc) < 96)%nat /\
  ~ In 0 (mc_reading mc).
Proof.
intros rd c mc (bs & HB & HE).
destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hf & Hlt & Hn0 & Hfz)).
unfold seg_spec.fldz, seg_spec.fld in Hf, Hfz. unfold seg_spec.SEG_M_SIZE in HL.
set (o := Z.to_nat seg_spec.MC_READING) in *. assert (Ho : Z.of_nat o = 9140) by reflexivity.
set (w := Z.to_nat 96) in *. assert (Hw : Z.of_nat w = 96) by reflexivity.
set (r := mc_reading mc) in *.
assert (HN : forall j, (j < S (length r))%nat -> nth j (r ++ [0]) 0 = bv_unsigned (nth (o + j) bs ZB0)).
{ intros j Hj. rewrite <- Hfz. rewrite nth_firstn. destruct (Nat.ltb_spec j (S (length r))) as [_|]; [|lia].
  unfold seg_spec.zs.
  rewrite (@List.nth_indep Z (map bv_unsigned (firstn w (skipn o bs))) j 0%Z (bv_unsigned ZB0))
    by (rewrite length_map, length_firstn, length_skipn; lia).
  rewrite map_nth. rewrite nth_firstn. destruct (Nat.ltb_spec j w) as [_|]; [|lia]. rewrite nth_skipn. reflexivity. }
split; [|split; [exact Hlt | exact Hn0]].
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite HN by lia.
replace (c + seg_spec.MC_READING + Z.of_nat j) with (c + Z.of_nat (o + j)) by (unfold seg_spec.MC_READING; lia).
apply HB. lia.
Qed.

(* the K cut's entry gi is an entry of the final model after the hit's model step m_upd *)
Lemma ki_h_gi_final : forall mcc gi f line rest fin,
  (gi < length (mc_seg mcc))%nat -> mf_fin (m_upd mcc gi f, Some gi) line rest = fin ->
  (gi < length (mc_seg fin))%nat.
Proof.
intros mcc gi f line rest fin Hgi Hfin. unfold mf_fin in Hfin.
destruct (ki_upd_cnt mcc gi f) as (HL & _).
assert (HC : mf_cur_ok (fst (m_upd mcc gi f, Some gi)) (snd (m_upd mcc gi f, Some gi)))
  by (cbn [fst snd]; unfold mf_cur_ok; rewrite HL; exact Hgi).
destruct (m_lines_ok (lines (mf_rest rest)) (m_upd mcc gi f, Some gi) (line + 1) HC) as [[G _] _].
rewrite Hfin in G. cbn [fst] in G. lia.
Qed.

(* b2z b is 0 or 1 *)
Lemma ki_h_b2z : forall b : bool, 0 <= seg_spec.b2z b <= 1.
Proof. intros [|]; unfold seg_spec.b2z; lia. Qed.

(* a register whose symbolic value the run left as the seed had it (atoms below 1024, read in the run's
   extended environment) *)
Lemma ki_h_keep_reg : forall E Ek (R0 R : list sv) (regs1 rr : bvmap 5 word) (r : bv 5),
  env_agree 1024 E Ek ->
  (forall r, getr regs1 r = sv_denot E (sr_get R0 r)) -> (forall r, getr rr r = sv_denot Ek (sr_get R r)) ->
  sv_eqb (sr_get R r) (sr_get R0 r) && sv_atoms_lt 1024 (sr_get R0 r) = true -> getr rr r = getr regs1 r.
Proof.
intros E Ek R0 R regs1 rr r HA H0 H1 Hq. apply andb_prop in Hq as [Hq Ha].
rewrite H0, H1. apply sv_eqb_eq in Hq. rewrite Hq. exact (sv_denot_agree 1024 E Ek _ HA Ha).
Qed.

(* the points and the run's state: the frame cells read-only, g's ignore and ignore_set at atom 37 (written) *)
Definition ki_h_slots : YP09.region :=
  YP09.mkRegion (Some 2%nat) 16 216 16 16 (YP09.r_chunks (mf_r_slots true true [])).
Definition ki_h_g : YP09.region := YP09.mkRegion (Some 37%nat) 24 32 24 32 [].
Definition ki_h_SH : list shent := [mkSHE 37 24 32].
Definition ki_h_facts : facts := mkFacts ((37%nat, HPTR 4) :: f_atoms mf_facts) [] [].
Definition ss_ki_h : sstate := mkSS KI_HIT sr_mf9 [ki_h_g; ki_h_slots] None ki_h_facts.

(* 4 bytes of the restricted memory read through the ASan reader *)
Lemma ki_h_sa_val4 : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 4 v -> sa_val (aview segs H mem) a 4 v.
Proof.
intros segs H mem a v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a register whose symbolic value is atom n + k *)
Lemma ki_h_reg : forall E ss (H : word -> bool) ms (r : bv 5) n k,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n k ->
getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. intros E ss H ms r n k HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
Lemma ki_h_reg_lit : forall E ss (H : word -> bool) ms (r : bv 5) z,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss H ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
(* a run of the hit's regions keeps every byte outside g's 8 bytes [g + 24, g + 32) *)
Lemma ki_h_keep : forall E rs (H : word -> bool) (m m' : word -> option byte) g,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
windows rs = [(Some 37%nat, 24, 32); (Some 2%nat, 16, 16)] ->
base_val E (Some 37%nat) = g ->
forall a, 0 <= a < 2 ^ 64 -> ~ (g + 24 <= a < g + 32) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' g HF Hw Hg a Ha Hn.
apply (kept_of_frame E rs H m m' (fun x => g + 24 <= x < g + 32) HF); [|exact Ha | exact Hn].
intros b wlo whi x Hin Hr. rewrite Hw in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; [rewrite Hg in Hr; exact Hr | lia].
Qed.
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Let RUN := paj_run B LAWS.

(* the state at snprintf's entry (the jal executed) *)
Definition ki_h_call_st (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(pos : Z) (gi : nat) (b : bool) (regs1 regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem3 md3 0 /\
(forall a, 0 <= a < 2 ^ 64 ->
 ~ (seg_spec.mseg_addr (mv_c v) gi + 24 <= a < seg_spec.mseg_addr (mv_c v) gi + 32) ->
 rdW Wc mem3 a = rdW Wc memc a) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + 24) 4 (seg_spec.b2z b) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + 28) 4 1 /\
getr regs3 1 = Z_to_bv 64 (BASE + KI_SNR) /\
getr regs3 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_IGNORE_FILE) /\ getr regs3 11 = w64 96 /\
getr regs3 12 = w64 (SegInstB.seg_litA_fz F_s) /\ getr regs3 13 = w64 (mv_c v + seg_spec.MC_READING) /\
(forall r : bv 5, In r ki_kregs -> getr regs3 r = getr regs1 r).

(* 0x86a18 to snprintf's entry *)
Lemma ki_h_run : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ov vl : nat) (vv : list Z) (b : bool),
ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
(gi < length (mc_seg (mf_final v)))%nat ->
getr regs1 20 = w64 (seg_spec.b2z b) ->
(forall regs3 mem3 md3, ki_h_call_st v lyc Sc Wc memc pos gi b regs1 regs3 mem3 md3 ->
  SRr SEGS Wc (mkCfg (mkst regs3 (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) mem3 (seg_rom SEGS)) md3)
    (MF_POST B v)) ->
mf_at B v Wc regs1 memc mdc KI_HIT.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB Hfin R20 KC.
destruct VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HMA & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
unfold mf_cur_ok in LCUR.
pose proof HMC as (bs & _ & (HL & HL32 & _)).
pose proof HMA as (CA0 & CA1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
(* the seed: the frame cells and 152(s1) (no scratch chunk), s9 pinned to atom 33 *)
pose proof (ki_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [] [] KI_HIT CX CORE CELLS RA LCUR NP Hnp
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS0) as HR0. cbn [ms_regs mkst ss_regs restrict] in HR0.
set (c := mv_c v) in *.
set (g := seg_spec.mseg_addr c gi).
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hgi32 : (gi < 32)%nat) by lia.
assert (HS1 : st_ok_pi SEGS VAL E (mkSS KI_HIT sr_mf9 [ki_h_slots] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KI_HIT)) memc (seg_rom SEGS)))).
{ refine (st_ok_pi_submem E _ _ [ki_h_slots] HS0 _ ltac:(vm_compute; reflexivity)).
  cbn [ss_mem]. unfold ki_regions, mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, ki_h_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks mf_r_slots].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros ch Hch. exact Hch. }
clear HS0.
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) np []) (Z_to_bv 64 0))
  by (intros; apply mfE_extra; assumption).
pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E33, E37. fold c in E33, E37. unfold mf_cur_ptr in E37. fold g in E37.
assert (E2 : ew E 2 = getr regs1 2) by exact (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl).
assert (E20 : ew E 20 = getr regs1 20) by exact (mfE_reg regs1 v lyc pos (Some gi) np [] 20 20%bv eq_refl).
pose proof RA as ((R2 & _) & _).
rewrite R2 in E2. rewrite R20 in E20. unfold w64 in E2, E20.
(* where things lie: the mconf block and s1 *)
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1r : alloc_ceiling + 8000 <= mf_s1 (mv_sp v) <= 2 ^ 47) by (destruct Ss1 as [E1 | E1]; rewrite E1; lia).
unfold seg_spec.SEG_M_SIZE in *.
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (B37 : base_val E (Some 37%nat) = g) by (cbn [base_val]; rewrite E37; apply unsigned_lit_small; lia).
(* the fact of atom 37 (g, 16-aligned: c mod 16 = 0): it decides the trap 0x86a20 *)
assert (Hg16 : g mod 16 = 0).
{ rewrite Hg. replace (c + 256 * Z.of_nat gi) with (c + 16 * Z.of_nat gi * 16) by ring.
  rewrite Z_mod_plus_full. exact Hc16. }
assert (F37 : afact_ok E 37 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E37, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hg16|]. lia. }
assert (HS2 : st_ok_pi SEGS VAL E (mkSS KI_HIT sr_mf9 [ki_h_slots] None ki_h_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KI_HIT)) memc (seg_rom SEGS))))
  by exact (st_ok_pi_add_fact E _ _ 37 _ HS1 F37).
clear HS1.
(* g's ignore / ignore_set (written) *)
assert (GOK : region_ok SEGS E (mrestrict (w_H Wc) memc) ki_h_g).
{ unfold region_ok, ki_h_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (g + o) ltac:(lia))). }
assert (HS : st_ok_pi SEGS VAL E ss_ki_h
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KI_HIT)) memc (seg_rom SEGS)))).
{ apply (st_ok_pi_add_region E _ _ ki_h_g HS2 eq_refl GOK).
  apply all_disjoint_of_extents. unfold ki_h_g, ki_h_slots, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi ss_mem]. rewrite B37, B2.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
clear HS2.
(* the shadow entry of the two inline checks: g->ignore and g->ignore_set *)
assert (SHOK : sh_ok SEGS (SOff 32 0) ki_h_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, ki_h_SH. apply Forall_cons; [|apply Forall_nil].
  pose proof HMA as (_ & _ & _ & HRAc & _).
  apply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 32 0) 37 c seg_spec.SEG_M_SIZE g 24 32 HRAc
    (mfE_U32 regs1 v lyc pos (Some gi) np []) (U_atom E 37 g E37 ltac:(lia)));
    [unfold seg_spec.SEG_M_SIZE in *; lia | unfold seg_spec.SEG_M_SIZE in *; lia |].
  intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE in *. lia. }
(* the writes the journal allows: g's 8 bytes lie in M_FILE_FP's entries and in the mconf block's heap block *)
assert (AWR : forall E', ew E' 37 = Z_to_bv 64 g ->
  awr_ok SEGS B E' [ki_h_g; ki_h_slots] SegInstB.STK_m_file (mv_sp v) (M_FILE_FP c (mv_k0 v) (mf_final v))
    (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)]).
{ intros E' E37'.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat g);
    [reflexivity | rewrite E37'; apply unsigned_lit_small; lia | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi ki_h_g] in Ha. right; left. split.
    + exists (c, seg_spec.mseg_addr c (length (mc_seg (mf_final v)))). split; [left; reflexivity|].
      cbn [fst snd]. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia.
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
(* 0x86a18 .. 0x86a74: cur & 3 = 0 (the trap 0x86a20 decided by the fact HPTR 4 of atom 37), the two checks
   (decided by ki_h_SH), the two stores, s9's reload, snprintf's arguments; the jal *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ exact (AWR E E37). }
(* the state at snprintf's entry: its environment agrees with E below the token atoms *)
lazymatch goal with HSx : st_ok _ ?Ex _ (restrict _ ?mB) |- _ => set (Ek := Ex) in *; rename mB into ms3 end.
assert (HAE : env_agree 1024 E Ek) by (unfold Ek; env_agree_chain (env_agree_refl 1024 E)).
assert (EE : forall n0, (n0 < 1024)%nat -> ew Ek n0 = ew E n0) by (intros n0 Hn0; exact (proj1 HAE n0 Hn0)).
(* the registers at the jal *)
lazymatch goal with HSx : st_ok _ Ek ?ssx (restrict _ ms3) |- _ =>
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms3) r = getr regs1 r)
    by (intros r Hin; apply (ki_h_keep_reg E Ek sr_mf9 (ss_regs ssx) regs1 (ms_regs ms3) r HAE HR0
          (fun r => st_ok_restrict_reg SEGS (w_H Wc) Ek ssx ms3 r HSx));
        unfold ki_kregs in Hin; cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]); destruct Hin);
  assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 -> (n0 < 1024)%nat ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
    by (intros r n0 k0 Hr0 Hn0; rewrite <- (EE n0 Hn0); exact (ki_h_reg Ek ssx (w_H Wc) ms3 r n0 k0 HSx Hr0));
  assert (QL : forall (r : bv 5) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms3) r = Z_to_bv 64 z)
    by (intros r z Hr0; exact (ki_h_reg_lit Ek ssx (w_H Wc) ms3 r z HSx Hr0))
end.
assert (QA : forall (r : bv 5) n0 x k0, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0) -> getr (ms_regs ms3) r = Z_to_bv 64 (x + k0))
  by (intros r n0 x k0 Hn0 Hx Hr0; rewrite Hr0, Hn0, unsigned_lit_small by exact Hx; reflexivity).
assert (HKS : KI_SNR = 7352) by reflexivity.
pose proof (QR 1%bv 240%nat KI_SNR eq_refl ltac:(lia)) as Q1.
rewrite (img_env_codeptr E HEI KI_SNR) in Q1.
pose proof (QA 10%bv 37%nat _ 156 E37 ltac:(lia) (QR 10%bv 37%nat 156 eq_refl ltac:(lia))) as Q10.
pose proof (QL 11%bv 96 eq_refl) as Q11.
pose proof (QR 12%bv 255%nat 0 eq_refl ltac:(lia)) as Q12.
pose proof (QA 13%bv 33%nat _ 9140 E33 ltac:(lia) (QR 13%bv 33%nat 9140 eq_refl ltac:(lia))) as Q13.
(* the bytes: kept outside g's 8 bytes; g->ignore = b2z b, g->ignore_set = 1 *)
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 24 <= a < g + 32) -> rdW Wc (ms_mem ms3) a = rdW Wc memc a).
{ intros a Ha Hna.
  lazymatch goal with
  | H1 : frame_of _ ?r1 (mrestrict _ memc) (mrestrict _ (ms_mem ms3)) |- _ =>
      exact (ki_h_keep _ r1 (w_H Wc) _ _ g H1 ltac:(vm_compute; reflexivity) B37 a Ha Hna)
  end. }
assert (UG : bv_unsigned (ew Ek 37) = g) by (rewrite (EE 37%nat ltac:(lia)), E37; apply unsigned_lit_small; lia).
lazymatch goal with HSx : st_ok _ Ek ?ssx (restrict _ ms3) |- _ =>
  pose proof (st_ok_region_nth Ek ssx (restrict (w_H Wc) ms3) 0 _ HSx eq_refl) as HRG end.
pose proof (ki_h_b2z b) as Hb01.
pose proof (field_of_region Ek _ 37 g _ _ _ _ _ 24 4%N (SOff 20 0) (seg_spec.b2z b) HRG UG
  ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat ltac:(lia)), E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity; rewrite H32; lia) ltac:(cbn; lia)) as VI.
pose proof (field_of_region Ek _ 37 g _ _ _ _ _ 28 4%N (SLit 1) 1 HRG UG
  ltac:(repeat (first [left; reflexivity | right]))
  eq_refl ltac:(assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity; rewrite H32; lia) ltac:(cbn; lia)) as VIS.
change (N.to_nat 4) with 4%nat in VI, VIS.
(* the call *)
pmkst HS.
assert (HFs : SegInstB.seg_litA_fz F_s = 0x21080) by (vm_compute; reflexivity).
apply KC. unfold ki_h_call_st, w64.
split; [exact HJ|].
split; [exact KP|].
split; [exact (ki_h_sa_val4 SEGS (w_H Wc) (ms_mem ms3) _ _ VI)|].
split; [exact (ki_h_sa_val4 SEGS (w_H Wc) (ms_mem ms3) _ _ VIS)|].
split; [exact Q1|].
split; [rewrite Q10; reflexivity|].
split; [rewrite Q11; reflexivity|].
split.
{ rewrite Q12. unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] 255 ltac:(unfold A_TEXT, A_LIM; lia)).
  change 255%nat with (A_OBJ 14). rewrite <- (mf_lit_obj VOBJS F_s 14 ltac:(left; reflexivity)).
  rewrite HFs, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
split; [rewrite Q13; reflexivity|].
exact KR.
Qed.

(* KI_HIT 0x86a18: the two stores into g = &c->seg[gi], snprintf of c->reading into g->ignore_file, then KI_SNR
   0x86a78 at the FP state snprintf returns *)
Lemma ki_s_hit : forall n, (forall fx0 : YK11.FPState, KI_DONE_stmt (fx := fx0) B KI_SNR n) -> KI_HIT_stmt B n.
Proof.
intros n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB FIN R20.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
unfold mf_cur_ok in LCUR.
assert (Hfin : (gi < length (mc_seg (mf_final v)))%nat)
  by exact (ki_h_gi_final mcc gi _ line rest (mf_final v) LCUR FIN).
apply (ki_h_run n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB Hfin R20).
intros regs3 mem3 md3 (HJ3 & KP3 & VI3 & VIS3 & Q1 & Q10 & Q11 & Q12 & Q13 & KR3).
pose proof (ki_regs_at_move B v lyc pos regs1 regs3 RA KR3) as RA3.
(* where things lie *)
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HJ3 as (HAR3 & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HMC as (bs0 & _ & (_ & HL32 & _)).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
assert (HF8 : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ assert (Hfin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin1) as (F1 & F2 & _).
  change (fs_frame_bytes 1) with 128 in F2. lia. }
assert (HFd : 0 <= frame_addr lyc 1 pos / 8 /\ frame_addr lyc 1 pos / 8 * 8 <= frame_addr lyc 1 pos)
  by (split; [apply Z.div_pos; lia | pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)); lia]).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs1r : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320) by (destruct Ss1 as [E1|E1]; rewrite E1; lia).
assert (HKS : KI_SNR = 7352) by reflexivity.
assert (HKK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
set (c := mv_c v) in *.
set (s1 := mf_s1 (mv_sp v)) in *.
set (g := seg_spec.mseg_addr c gi) in *.
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hgi32 : (gi < 32)%nat) by lia.
unfold seg_spec.SEG_M_SIZE in *.
(* c->reading, at the call state too; snprintf_s 96 "%s" [reading] = reading *)
destruct (ki_h_reading _ _ _ HMC) as (HZR & Hrl & Hr0).
set (r := mc_reading mcc) in *.
rewrite (ki_snp_reading r Hrl Hr0) in FIN.
assert (HZR3 : sa_zs (rdW Wc mem3) (c + seg_spec.MC_READING) (r ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite KP3; [exact (HZR j ltac:(rewrite length_app; cbn [length]; lia)) | unfold seg_spec.MC_READING; lia
    | unfold seg_spec.MC_READING; lia]. }
assert (HSA3 : sa_addr (rdW Wc mem3) c 9236).
{ destruct HMA as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia. }
assert (HST3 : sa_tail (rdW Wc mem3) (c + 9236 - 1)).
{ intros x Hx. pose proof (Z.mod_pos_bound (c + 9236 - 1) 8 ltac:(lia)).
  rewrite KP3; [exact (HMT x Hx) | lia | lia]. }
(* 0x86a74: snprintf(g->ignore_file, 96, "%s", c->reading) *)
pose proof RA3 as ((R2 & R3 & R4 & _) & _).
apply (mf_snp_field_call B SSP ASNPRINTF (mf_rod_now_j B RELRO) (mf_lit_now_j B) v lyc Sc Wc regs3 mem3 md3 pos
  gi r seg_spec.MS_IGNORE_FILE KI_SNR (or_intror eq_refl) CX LS FRM HJ3 HPerm HSA3 HST3 HZR3 Hrl Hr0 Hgi32 Hfin
  R2 R3 R4 Q1 ltac:(rewrite HKS; lia) ltac:(rewrite HKS; reflexivity) Q10 Q11 Q12 Q13).
intros fx1 regs2 mem2 md2 Hfx HJ2 HP2 HZF HK2.
rewrite HKK in HK2. fold c s1 in HK2, HZF. fold g in HK2, HZF.
set (d := g + seg_spec.MS_IGNORE_FILE) in *.
assert (Hd : d = g + 156) by reflexivity.
(* what 0x86a18 .. 0x86a74 and snprintf wrote: g's ignore / ignore_set, snprintf's window, the field *)
set (RW := fun a => (g + 24 <= a < g + 32) \/ (s1 - 8192 <= a < s1) \/ (d <= a < d + Z.of_nat (length r) + 1)).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha HR. rewrite (HK2 a Ha); [apply KP3; [exact Ha|] | |]; intros Hc; apply HR; unfold RW; tauto. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a [Ha | [Ha | Ha]]; unfold mf_rw, seg_spec.SEG_M_SIZE; rewrite HSTK; fold s1 c.
  - right; left. lia.
  - left. lia.
  - right; left. lia. }
assert (RWS : mf_rws v RW).
{ intros a HR Ha. exfalso. fold s1 in Ha. destruct HR as [H | [H | H]]; lia. }
assert (NRW_lo : forall a, a < alloc_ceiling -> ~ (c <= a < c + 9236) -> ~ RW a).
{ intros a H1 H2 [H | [H | H]]; lia. }
assert (NRW_hi : forall a, s1 <= a -> ~ RW a).
{ intros a H1 [H | [H | H]]; lia. }
(* the block after the three writes holds mcc' *)
set (mcc' := m_upd mcc gi (ms_with_ignore b r)) in *.
assert (MC2 : sa_mconf (rdW Wc mem2) c mcc').
{ apply (ki_e_mconf_ign (rdW Wc memc) (rdW Wc mem2) c mcc gi b r HMC LCUR Hrl Hr0).
  - intros x Hx H1 H2. fold g in H1, H2. unfold seg_spec.SEG_M_SIZE in Hx.
    apply K; [lia|]. intros [H | [H | H]]; lia.
  - fold g. intros kk Hkk. rewrite HK2; [exact (VI3 kk Hkk) | lia | lia | lia].
  - fold g. intros kk Hkk. rewrite HK2; [exact (VIS3 kk Hkk) | lia | lia | lia].
  - exact HZF.
  - intros x z Hx. exact (ki_aview_byte SEGS (w_H Wc) mem2 x z Hx). }
(* every cut fact at the return *)
assert (VKEEP : forall a nb x, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall kk, 0 <= kk < Z.of_nat nb -> ~ RW (a + kk)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a nb x -> val_mem SEGS (mrestrict (w_H Wc) mem2) a nb x)
  by (intros a nb x H0 H1 H2 V; exact (mf_val_keep Wc Wc memc mem2 RW a nb x K H0 H1 H2 V)).
assert (CORE2 : mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_ON mcc').
{ apply (mf_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Sc Wc mem2 md2 RW MF_LOW_ON mcc' CX CORE HJ2
    (Permutation_refl _) K RWok); [| |exact MC2].
  - intros ii Hii. apply VKEEP; [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH ii Hii)].
    intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk. apply NRW_lo; unfold SHADOW_OFF in *; lia.
  - apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact V120].
    intros kk Hkk. apply NRW_hi. lia. }
assert (CELLS2 : mf_cells v lyc pos mem2 Wc (Some gi)).
{ apply (mf_keep_cells B v lyc pos Wc Wc memc mem2 RW (Some gi) (Some gi) CX K RWS CELLS).
  pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
  apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact V136].
  intros kk Hkk. apply NRW_hi. lia. }
assert (LOOP2 : mf_loop v Wc mem2 mcc (Some gi) line p rest)
  by exact (mf_loop_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Sc Wc mem2 md2 RW mcc (Some gi) line p rest CX CORE HJ2
    (Permutation_refl _) K RWok LOOP).
assert (NP2 : mf_np v mem2 Wc (mf_next p rest)).
{ unfold mf_np, mf_slot in NP |- *. apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros kk Hkk. apply NRW_hi. lia. }
destruct (ki_upd_cnt mcc gi (ms_with_ignore b r)) as (U1 & U2 & U3 & U4 & _).
fold mcc' in U1, U2, U3, U4.
assert (G : forall rr, acallee_saved rr -> getr regs2 (Z_to_bv 5 rr) = getr regs3 (Z_to_bv 5 rr)) by exact HP2.
assert (P27 : getr regs2 27 = getr regs3 27) by exact (G 27 ltac:(unfold acallee_saved; lia)).
(* KI_SNR 0x86a78 at the FP state fx1: the block holds mcc', the line's model mcl = mcc *)
apply (KD fx1 v lyc Sc Wc regs2 mem2 md2 pos mcc' mcc gi line p rest CX LS (fxrel_frm0 fx fx1 FRM Hfx) CORE2 CELLS2
  (mf_regs_keep B v lyc pos regs3 regs2 RA3 HP2) Hn Hr LOOP2).
- rewrite U3. lia.
- rewrite U4. lia.
- rewrite U2. lia.
- rewrite U1. exact LCUR.
- exact FIN.
- rewrite P27, (KR3 27%bv ltac:(unfold ki_kregs; cbn [In]; tauto)). exact R27.
- exact NP2.
Qed.
End e.
End f.
End d.
About ki_s_hit.
Print Assumptions ki_s_hit.
