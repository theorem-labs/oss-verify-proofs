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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 251 of its 288 lines of code are new or changed and 416 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the ONE shared snprintf call step of the m_file segment walks
   S_MF_KROLE and S_MF_KIGNP, stated over m_file_m.v's cut predicates. The KIGNP segment lane of the G2 walk owner's G2.
   proves no function (kind: segment lemma of m_file's walk: the shared snprintf call step of S_MF_KROLE / S_MF_KIGNP).

   mf_snp_field_call: the call snprintf(g + off, 96, "%s", c->reading) at 0x86934 (S_MF_KROLE, off =
   seg_spec.MS_ROLE_FILE = 0x3c, g->role_file) and 0x86a34 (S_MF_KIGNP, off = seg_spec.MS_IGNORE_FILE = 0x9c,
   g->ignore_file), from the state at the wrapper's entry (the `jal` executed: pc = SIGMA
   SS___interceptor_trampoline_snprintf, ra = BASE + ret, sp = s1, a0 = g + off with g = mseg_addr c gi, a1 = 96,
   a2 = the literal "%s" (seg_litA_fz F_s), a3 = c + MC_READING = c->reading, a C string r of fewer than 96 bytes).
   The contract is RtFormat.asnprintf_realizes (= RtPFCmd.asnprintf_sh, the shared snprintf text at FR_cmd with the
   window CMD_SNP_K = 2 * ESTACK) at the walk's FP state, whose rounding mode is 0 (sa_frm0). Its post is
   FP-existential: PaFx.v srr_art_postF_of_pf turns it into art_postF, aj_art_own_atF takes the journal step (the
   destination lies in M_FILE_FP's first range [c, mseg_addr c |seg|) and in the live mconf block: awr_byte's
   second arm) and srr_after_artF continues at the FP state fx1 the wrapper returns. Since |r| < 96, snprintf writes
   all of r and its NUL at g + off (sn_bytes 95 r = r ++ [0]); nothing else changes outside the callee's window
   [s1 - CMD_SNP_K, s1).
   Where things lie: [g + off, g + off + 96) ends at most at c + 31 * 256 + 0x9c + 96 = c + 0x1ffc, below
   c->reading at c + 0x23b4, so the destination and the source are apart inside the block; the block lies below
   the allocator ceiling, s1 - CMD_SNP_K at least 64 bytes above it (STK_m_file = 8560 >= 8192 + 304), and off
   the image (SegPaLib.blk_off_imgP), which gives the contract's dest_off_globals and keeps the read-only list
   CMD_SNP_CR, the stack-protector cells and the format off the written regions. The bytes past r's NUL up to
   str_end (the word-at-a-time slack) are block bytes or the block's sa_tail (c mod 8 = 0); their amem_range comes
   from the block's in_app with 7 bytes of slack past its end (both arms of in_app leave that room below
   kLowMemEnd and kHighMemEnd).
   The one fact of the contract's format family that only a computation over the image gives (as RtPFCmd.fr_lit_ok
   at fuzz_command's call sites): the format "%s" at image A 0x21080 lies at or above CMD_IMG_LO and its NUL below
   CMD_GOTW (sn_fmt_nums). The family's string-argument facts (cmd_args_slack / cmd_args_amem) are given here
   (FR_cmd_intro does not apply: it forbids string arguments).
   Section hypotheses: the m_file cut-statement lane's shared list (LAWS a Let; SSP, RELRO, RO), the snprintf contract at every FP
   state; the current-state facts are lib/A/Prog/m_file_k.v's journal forms mf_rod_now_j / mf_lit_now_j (at the call
   the block no longer holds an mconf the walk names, so the lemma takes no mf_core). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd RtPFShared RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_k m_file_iq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the format "%s" and its address at image A *)
Lemma sn_fs : F_s = [37; 115].
Proof. vm_compute. reflexivity. Qed.
Lemma sn_fs_at : SegInstA.seg_litA_fz F_s = 0x21080.
Proof. vm_compute. reflexivity. Qed.
(* the format family's image bounds at this call, by computation (RtPFCmd.fr_lit_ok's first two checks) *)
Lemma sn_fmt_nums : RtPFCmd.CMD_IMG_LO <= SegInstA.seg_litA_fz F_s /\
  SegInstA.seg_litA_fz F_s + Z.of_nat (length F_s) + 1 <= RtPFCmd.CMD_GOTW.
Proof. rewrite sn_fs_at, sn_fs. unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_GOTW. cbn [length]. lia. Qed.
(* the image range of dest_off_globals and the read-only list lie inside [0x10000, kImgEnd = 0x601000] *)
Lemma sn_img_bounds : 0x10000 <= RtPFCmd.CMD_IMG_LO /\ RtPFCmd.CMD_IMG_HI <= 0x601000.
Proof. unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, kImgEnd. lia. Qed.
Lemma sn_cr_img : forall x, In x RtPFCmd.CMD_SNP_CR ->
  RtPFCmd.CMD_IMG_LO <= fst x /\ 0 <= snd x /\ fst x + snd x <= RtPFCmd.CMD_IMG_HI.
Proof.
intros x Hx. pose proof RtPFCmd.cmd_snp_cr_img as H. rewrite forallb_forall in H. specialize (H x Hx).
unfold RtPFCmd.in_cmd_img in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
(* the word-at-a-time end of a C string ending at P is below that of one ending at E >= P *)
Lemma sn_str_end_le : forall P E x, P <= E -> P < x < P - P mod 8 + 8 -> x < E - E mod 8 + 8.
Proof.
intros P E x HPE Hx.
pose proof (Z.div_mod P 8 ltac:(lia)). pose proof (Z.mod_pos_bound P 8 ltac:(lia)).
pose proof (Z.div_mod E 8 ltac:(lia)). pose proof (Z.mod_pos_bound E 8 ltac:(lia)).
lia.
Qed.
Lemma sn_str_end_bnd : forall w (s : list Z),
  w + Z.of_nat (length s) + 1 <= RtPFShared.str_end w s <= w + Z.of_nat (length s) + 8.
Proof.
intros w s. unfold RtPFShared.str_end.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.

Local Ltac sn_dj := unfold zdisjoint; cbn [fst snd]; lia.
Local Ltac sn_f2 := apply Forall_cons; [sn_dj | apply Forall_cons; [sn_dj | apply Forall_nil]].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a range of an application range [p, p + n) below the allocator ceiling, or reaching at most 8 bytes past its
   end, is in amem_range: both arms of in_app leave that room *)
Lemma sn_amem_app : forall p n lo k, in_app p n -> p <= lo -> 0 <= k -> lo + k <= p + n + 8 -> amem_range lo k.
Proof.
intros p n lo k [H1 [H2 | [H2 H3]]] Hlo Hk Hhi; unfold amem_range.
- left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
- right. pose proof ASAN_CEIL_range as [[A1 A2] _]. unfold kHighMemBeg, kHighMemEnd in *. lia.
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
(* the shared Section hypotheses (the m_file cut-statement lane's ruling (a), amended 17:1xZ) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Context {RO : ro_below_ofl SEGS SegInstA.RLO_A SegInstA.RHI_A}.
(* the callee, at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) SegInstA.gotwA
    SegInstA.guardA.

(* snprintf(g + off, 96, "%s", c->reading) from the wrapper's entry: r ++ [0] at g + off, at BASE + ret, at the FP
   state the wrapper returns, nothing else changed outside the callee's window *)
Lemma mf_snp_field_call : forall v lyc Sc Wc (regsc : bvmap 5 word) memc mdc pos (gi : nat) (r : list Z) (off ret : Z),
  off = seg_spec.MS_ROLE_FILE \/ off = seg_spec.MS_IGNORE_FILE ->
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
  Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
  sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE -> sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1) ->
  sa_zs (rdW Wc memc) (mv_c v + seg_spec.MC_READING) (r ++ [0]) -> (length r < 96)%nat -> ~ In 0 r ->
  (gi < 32)%nat -> (gi < length (mc_seg (mf_final v)))%nat ->
  getr regsc 2 = w64 (mf_s1 (mv_sp v)) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regsc 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + off) -> getr regsc 11 = w64 96 ->
  getr regsc 12 = w64 (SegInstA.seg_litA_fz F_s) -> getr regsc 13 = w64 (mv_c v + seg_spec.MC_READING) ->
  (forall (fx1 : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2,
    fxrel fx fx1 ->
    ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
      (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
    aregs_preserved regsc regs2 ->
    sa_zs (rdW Wc mem2) (seg_spec.mseg_addr (mv_c v) gi + off) (r ++ [0]) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - RtPFCmd.CMD_SNP_K <= a < mf_s1 (mv_sp v)) ->
      ~ (seg_spec.mseg_addr (mv_c v) gi + off <= a < seg_spec.mseg_addr (mv_c v) gi + off + Z.of_nat (length r) + 1) ->
      rdW Wc mem2 a = rdW Wc memc a) ->
    SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST (fx := fx1) B v)) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memc (seg_rom SEGS)) mdc)
    (MF_POST B v).
Proof.
intros v lyc Sc Wc regsc memc mdc pos gi r off ret Hoff CX LS FRM HJ HPm HSA HST HZS Hrl Hr0 Hg32 Hgl
  R2 R3 R4 R1 Hret Hret2 R10 R11 R12 R13 KC.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSM : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMR : seg_spec.MC_READING = 9140) by reflexivity.
assert (Hd : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi) by reflexivity.
assert (Hoffb : 60 <= off <= 156)
  by (destruct Hoff as [E | E]; rewrite E; unfold seg_spec.MS_ROLE_FILE, seg_spec.MS_IGNORE_FILE; lia).
clear Hoff.
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & Ho16).
assert (Hs1r : mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) by lia.
clear Hs1.
(* the mconf block: live at the call, below the allocator ceiling, off the image *)
destruct HCH as (b & m & Hin0 & Hbc & Hec).
assert (Hin : In (b, m) (ablocks B lyc Sc)) by exact (Permutation_in _ (Permutation_sym HPm) Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hin) as Hoffimg.
assert (Hcb : b <= mv_c v /\ mv_c v + 9236 <= b + req_size m) by lia.
assert (Hoi : 0x601000 <= mv_c v \/ mv_c v + 9236 <= 0x10000) by (unfold off_img in Hoffimg; lia).
clear Hoffimg.
assert (Hs1b : mv_c v + 9244 <= mf_s1 (mv_sp v) - 8192 /\ mf_s1 (mv_sp v) <= 2 ^ 47) by lia.
assert (Hsp : spZ regsc = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hsp' : spZ regsc = mf_s1 (mv_sp v)) by lia.
(* the text: fewer than 96 bytes, so the written part is all of it and its NUL *)
assert (Hsn : RtPFShared.sn_bytes (96 - 1) r = r ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity | lia]. }
assert (Hsl : RtPFShared.sn_len (96 - 1) r = Z.of_nat (length r) + 1).
{ unfold RtPFShared.sn_len. rewrite Hsn, length_app. cbn [length]. lia. }
(* the facts the contract reads at the call state *)
pose proof (mf_rod_now_j B RELRO v lyc Sc Wc memc mdc pos CX HJ) as HROD.
pose proof (mf_lit_now_j B v lyc Sc Wc memc mdc pos F_s CX HJ ltac:(unfold M_FILE_LITS; left; reflexivity))
  as (Hf0 & ((HFZ & _) & _) & HFP & _ & _).
destruct (HFP lyc Sc Wc memc mdc HAR) as (_ & _ & FAM & FRA & FHV).
clear HFP.
destruct (SSP lyc Sc Wc memc mdc HAR) as (HG1 & cval & HG2).
pose proof sn_fmt_nums as (FN1 & FN2).
pose proof sn_img_bounds as (I1 & I2).
assert (HFL : Z.of_nat (length F_s) = 2) by (rewrite sn_fs; reflexivity).
rewrite HFL in FAM, FRA, FHV.
set (f := SegInstA.seg_litA_fz F_s) in *.
assert (Hf : f = 0x21080) by exact sn_fs_at.
assert (HraT : YK0s.ret_ok (getr regsc 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | exact Hret2]).
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K SegInstA.STK_m_file (mv_sp v)
  (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
  lyc Sc Wc memc mdc 0 regsc (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp Ho16 ltac:(lia) ltac:(rewrite HK, Hes; lia)
  ltac:(rewrite HK, HSTK; lia) HraT R3 R4) as (EPRE & ESTK & EPRES).
(* a3 = c->reading *)
assert (HA3 : argZ regsc 3 = mv_c v + seg_spec.MC_READING).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R13. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* 0x86934 / 0x86a34: snprintf(g + off, 96, "%s", c->reading) writes r and its NUL into the block *)
unfold MF_POST.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
    (fun a => seg_spec.mseg_addr (mv_c v) gi + off <= a < seg_spec.mseg_addr (mv_c v) gi + off
      + RtPFShared.sn_len (96 - 1) r)
    (SIGMA SS___interceptor_trampoline_snprintf) Wc regsc memc SegInstA.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdc 0 (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + ret)) _ HJ Hsp Ho16 ltac:(lia) ltac:(lia)
    ltac:(rewrite HK, HSTK; lia) R1).
  - (* the written cells: M_FILE_FP's first range, inside the live block *)
    intros a Ha. cbv beta in Ha. rewrite Hsl, Hd in Ha. unfold awr_byte. right; left. split.
    + exists (mv_c v, seg_spec.mseg_addr (mv_c v) (length (mc_seg (mf_final v)))).
      split; [unfold M_FILE_FP; left; reflexivity|]. cbn [fst snd].
      unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia.
    + exists b, m. split; [exact Hin | lia].
  - apply srr_art_postF_of_pf; [exact EPRES|].
    apply (ASNPRINTF fx lyc Sc Wc regsc memc mdc (seg_spec.mseg_addr (mv_c v) gi + off) 96 f []
      (map (argZ regsc) [3; 4; 5; 6; 7] ++ []) r cval).
    + exact EPRE.
    + exact ESTK.
    + exact EPRES.
    + exact R10.
    + exact R11.
    + exact R12.
    + (* rt_rom_view: the unowned read-only bytes, arodata_okP's left disjunct *)
      intros a Ha Hn He. apply HROD; [left; exact Ha | exact Hn | exact He].
    + apply Forall_forall. intros x Hx. destruct (sn_cr_img x Hx) as (X1 & X2 & X3). lia.
    + apply Forall_forall. intros x Hx. destruct (sn_cr_img x Hx) as (X1 & X2 & X3).
      unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. sn_f2.
    + exact HG1.
    + exact HG2.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. unfold SegInstA.gotwA. sn_f2.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. unfold SegInstA.guardA. sn_f2.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length]. rewrite Hsp'. lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. cbn [length]. sn_f2.
    + (* FR_cmd: the format "%s", one string argument c->reading *)
      unfold RtPFCmd.FR_cmd. exists F_s, [RtPFPf.Ps], [RtPFPf.APtr r].
      split.
      { (* fmt_at *)
        split; [lia|]. split.
        { intros i Hi. rewrite HFL in Hi.
          replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HFZ (Z.to_nat i)) by (rewrite length_app, sn_fs; cbn [length]; lia). reflexivity. }
        rewrite HFL. split.
        { unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. sn_f2. }
        split; [exact FAM|]. split; [exact FRA | exact (FHV ltac:(lia))]. }
      split; [rewrite sn_fs; reflexivity|].
      split; [apply Forall_cons; [exact I | apply Forall_nil]|].
      split.
      { cbn [map app RtPFShared.pf_args_asan]. split; [|exact I].
        cbn [RtPFShared.pf_arg_asan]. rewrite HA3.
        split.
        { apply Forall_forall. intros x Hx. destruct (In_nth r x 0 Hx) as (i & Hi & Hn).
          pose proof (HZS i ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
          rewrite app_nth1 in Hv by exact Hi. rewrite Hn in Hv.
          destruct (aview_byte SEGS _ _ _ _ Hv) as (_ & _ & _ & Hb).
          assert (x <> 0) by (intros ->; exact (Hr0 Hx)). lia. }
        split; [lia|]. split; [lia|]. split.
        { intros i Hi. replace (mv_c v + seg_spec.MC_READING + i)
            with (mv_c v + seg_spec.MC_READING + Z.of_nat (Z.to_nat i)) by lia.
          apply HZS. rewrite length_app. cbn [length]. lia. }
        split.
        { (* the slack after the NUL: block bytes, then the block's tail *)
          intros x Hx. destruct (Z.lt_ge_cases x (mv_c v + seg_spec.SEG_M_SIZE)) as [Hlt | Hge].
          - apply (aview_some_of_apresent SEGS). apply (proj1 (Hbpres x ltac:(lia))).
          - unfold RtPFShared.str_end in Hx. apply HST. split; [lia|].
            apply (sn_str_end_le (mv_c v + seg_spec.MC_READING + Z.of_nat (length r))); [lia | exact Hx]. }
        split.
        { pose proof (sn_str_end_bnd (mv_c v + seg_spec.MC_READING) r) as (SE1 & SE2).
          unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. sn_f2. }
        split.
        { apply (sn_amem_app b (req_size m)); [exact Hbapp | lia | lia | lia]. }
        split.
        { apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | lia | lia]. }
        { apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | lia | lia | lia]. } }
      split.
      { cbn [RtPFPf.pf_text option_map]. rewrite app_nil_r. reflexivity. }
      split; [exact I|].
      split; [exact FN1|]. split; [exact FN2|].
      split.
      { cbn [map app RtPFCmd.cmd_args_slack]. rewrite HA3. split; [|exact I].
        pose proof (sn_str_end_bnd (mv_c v + seg_spec.MC_READING) r) as (SE1 & SE2).
        apply (sn_amem_app b (req_size m)); [exact Hbapp | lia | lia | lia]. }
      split; [rewrite sn_fs; discriminate|].
      { cbn [map app RtPFCmd.cmd_args_amem]. rewrite HA3. split; [|exact I].
        apply (sn_amem_app b (req_size m)); [exact Hbapp | lia | lia | lia]. }
    + lia.
    + lia.
    + rewrite Hd. lia.
    + rewrite Hsl, Hd. lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl, Hd. cbn [pairwise].
      split; [|split; [apply Forall_nil | exact I]]. apply Forall_cons; [sn_dj | apply Forall_nil].
    + (* dest_ok: block bytes the runtime does not own, below the callee's window *)
      intros a Ha. rewrite Hsl, Hd in Ha. destruct (Hbpres a ltac:(lia)) as [Hpr Hno].
      split; [exact (apresent_writable SEGS _ _ _ Hpr)|]. split; [exact Hno|]. rewrite Hsp', Hes. lia.
    + rewrite Hsl, Hd. apply (sn_amem_app b (req_size m)); [exact Hbapp | lia | lia | lia].
    + apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | | ];
        rewrite ?Hsl, ?Hd; lia.
    + apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | | | ];
        rewrite ?Hsl, ?Hd; lia.
    + (* dest_off_globals: the block is off the image *)
      rewrite Hsl, Hd. sn_dj.
    + exact FRM. }
(* back at BASE + ret at the FP state fx1 the wrapper returns *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HA0 & HBY) & HK2).
apply (KC fx1 regs2 mem2 md2 Hfx HJ2 HP2).
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HBY (Z.of_nat i)) by (rewrite Hsl; lia).
  rewrite Hsn, Nat2Z.id. reflexivity.
- intros a Ha Hw Hdst. apply (HK2 a Ha).
  + intros Hc. apply Hw. lia.
  + intros Hc. apply Hdst. rewrite Hsl in Hc. lia.
Qed.
End e.
End f.
End d.
