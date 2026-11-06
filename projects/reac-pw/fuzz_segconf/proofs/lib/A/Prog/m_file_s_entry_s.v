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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 249 of its 293 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, m_file at 0x85ebc): the snprintf call step of m_file's segment
   S_MF_ENTRY, at 0x86014 (listing offset AF_m_file + 0x158, `jal ra, snprintf's trampoline`) to its return 0x86018
   (AF_m_file + 0x15c): snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf"). Proves no function: one
   segment lemma, mf_snp_step, for the segment's walk (lib/A/Prog/m_file_s_entry.v).
   The pattern is plugin-hostd/fuzz_command's check_reply_s4.v:234-460 (commit 501c0d516c69) and image
   A's m_refuseA.v mr_snp: a symbolic run of the one `jal` from a seed with no region (the registers as atoms), the
   shared snprintf contract (RtFormat.asnprintf_realizes = RtPFCmd.asnprintf_sh) through PaFx.v's
   srr_art_postF_of_pf, the journal step aj_art_own_atF with the footprint arm of awr_byte (c->reading lies in
   M_FILE_FP's fifth range and in the mconf block, a live heap block), and srr_after_artF to the continuation at the
   FP state the wrapper returns. The family FR_cmd is built by hand (its fr_lit_ok helper refuses a string
   argument): fmt_at from m_file_s_entry_k.v's mf_fmt_lit, the %s argument from mf_label_arg, the destination from
   mf_dest_heap and the block lemmas; the text the wrapper writes is snprintf_s 96 F_s [AS ltext]
   (m_file_s_entry_m.v mf_sn_bytes). The call's pc numbers are written as AF_m_file + 0x158 / + 0x15c here, the
   values of m_file_s_entry.v's MF_SNP / MF_RET_SNP, so that m_file_s_entry.v can Require this file. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFCmd RtPFShared RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_m m_file_s_entry_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* an opaque wrapper for a disjunctive address fact: lia does not case-split under it *)
Definition mfs_nam (P : Prop) : Prop := P.

(* ---- reader facts carried to a reader that agrees at every address ---- *)
Lemma mfs_str_eq : forall (rd rd' : reader) p s, (forall a, rd' a = rd a) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s E ((Hz & Hn) & Ht). split; [split|].
- intros i Hi. rewrite E. exact (Hz i Hi).
- exact Hn.
- intros x Hx. rewrite E. exact (Ht x Hx).
Qed.
Lemma mfs_addr_eq : forall (rd rd' : reader) q n, (forall a, rd' a = rd a) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n E (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Ho). exists s. rewrite E. exact (conj Hs Ho).
- intros Hpos s Hs. rewrite E. exact (A4 Hpos s Hs).
Qed.
Lemma mfs_argZ3 : forall regs : bvmap 5 word, argZ regs 3 = bv_unsigned (getr regs 13).
Proof.
intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite E. reflexivity.
Qed.
Lemma mfs_parse : RtPFPf.pf_parse F_s = Some [RtPFPf.Ps].
Proof. vm_compute. reflexivity. Qed.
Lemma mfs_text : forall s, RtPFPf.pf_text [RtPFPf.Ps] [RtPFPf.APtr s] = Some s.
Proof. intros s. cbn [RtPFPf.pf_text option_map]. rewrite app_nil_r. reflexivity. Qed.
Lemma mfs_fs_lit : SegInstA.seg_litA_fz F_s = 0x21080.
Proof. vm_compute. reflexivity. Qed.
Lemma mfs_fs_len : length F_s = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma mfs_lit_eq : forall segs B (rd rd' : reader) a s, (forall x, rd' x = rd x) -> sa_lit segs B rd a s ->
  sa_lit segs B rd' a s.
Proof.
intros segs B rd rd' a s E (L0 & L1 & L2 & L3 & L4).
exact (conj L0 (conj (mfs_str_eq rd rd' a s E L1) (conj L2 (conj L3 L4)))).
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
(* the snprintf wrapper (the interceptor-layer owner's interface row 4), at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) SegInstA.gotwA SegInstA.guardA.
(* the stack-protector cells musl's printf_core reads, at every state whose AR holds *)
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.

Lemma mf_snp_step : forall (v : mfv) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos
  (lptr : Z) (ltext : list Z),
mf_cx B v -> sa_frm0 ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
(* the registers at 0x86014: sp = s1, gp, tp, a0 = &c->reading, a1 = 96, a2 = "%s", a3 = the text's pointer *)
getr regs1 2 = w64 (mf_s1 (mv_sp v)) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 10 = w64 (mv_c v + seg_spec.MC_READING) -> getr regs1 11 = w64 96 ->
getr regs1 12 = w64 (SegInstA.seg_litA_fz F_s) -> getr regs1 13 = w64 lptr ->
(* (ra is not a premise: the jal at 0x86014 sets it) *)
(* what the wrapper prints: a C string at lptr, in a heap block, a live side-stack frame or the image, apart
   from the destination *)
0 < lptr -> sa_str (rdW Wc memc) lptr ltext -> sa_addr (rdW Wc memc) lptr (Z.of_nat (length ltext) + 1) ->
Z.of_nat (length ltext) <= 65535 ->
(sa_heap B lyc Sc lptr (Z.of_nat (length ltext) + 1) \/ sa_fframe lyc Sc lptr (Z.of_nat (length ltext) + 1) \/
 sa_img SEGS B lptr (Z.of_nat (length ltext) + 1)) ->
sa_disj lptr (seg_spec.cstr_span lptr ltext) (mv_c v + seg_spec.MC_READING) 96 ->
(* the destination and the format at this state *)
sa_heap B lyc Sc (mv_c v) seg_spec.SEG_M_SIZE ->
sa_lit SEGS B (rdW Wc memc) (SegInstA.seg_litA_fz F_s) F_s ->
RtDefs.rt_rom_view SEGS B Wc memc ->
(* the continuation, at the FP state the wrapper returns *)
(forall (fx1 : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2,
   PaFx.fxrel fx fx1 -> aregs_preserved regs1 regs2 ->
   ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
     (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
   (* c->reading holds the model's text and its NUL, and its 96 bytes are readable *)
   (forall i, (i < S (length (snprintf_s 96 F_s [AS ltext])))%nat ->
      rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) =
      Some (nth i (snprintf_s 96 F_s [AS ltext] ++ [0]) 0)) ->
   (forall i, (i < 96)%nat -> rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) <> None) ->
   (* every byte outside c->reading and the wrapper's stack window is kept *)
   (forall a, 0 <= a < 2 ^ 64 ->
      ~ (mv_c v + seg_spec.MC_READING <= a < mv_c v + seg_spec.MC_READING + 96) ->
      ~ (mf_s1 (mv_sp v) - 2 * ESTACK <= a < mf_s1 (mv_sp v)) -> rdW Wc mem2 a = rdW Wc memc a) ->
   SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (w64 (BASE + (AF_m_file + 0x15c))) mem2 (seg_rom SEGS)) md2)
     (MF_POST (fx := fx1) B v)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_m_file + 0x158))) memc (seg_rom SEGS)) mdc)
  (MF_POST B v).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lptr ltext CX HFRM HJ0 R2 R3 R4 R10 R11 R12 R13
  Hlp0 HSTR HADDR Hlen HLOC HDJ HHEAP HLIT HROD HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs1m32 & Hsp0c).
destruct (mf_sp0 B v CX) as (_ & Hsp47 & Hsp16).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HKK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
assert (Ho16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E1 | E1]; rewrite E1;
      [replace (mv_sp v - 288 - mv_sp v) with (-288) by lia | replace (mv_sp v - 304 - mv_sp v) with (-304) by lia];
      reflexivity).
assert (Hs1b : mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) by (destruct Hs1 as [E1 | E1]; lia).
(* the seed at the call: every register an atom, no region, no fact *)
set (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_m_file + 0x158) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (AF_m_file + 0x158))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HAG : env_agree 32 (Ereg regs1 []) E)
  by (split; [intros k Hk; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
pose proof HJ0 as HJ.
(* 0x86014: jal snprintf's trampoline; the run stops at the trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdv := dM) in *; clearbody mdv end.
assert (HMEQ : forall x : word, ms_mem ms x = memc x)
  by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a; unfold aview, mbyte, mrestrict; rewrite HMEQ; reflexivity).
clear HF HFr HG.
pose proof (proj1 HJ) as HARt.
(* the registers at the trampoline: the jal wrote ra, every other register is the call's *)
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 [] ([2; 3; 4; 10; 11; 12; 13]%bv : list (bv 5)) HS HAG
  ltac:(vm_compute; reflexivity)) as KR.
assert (T2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v)))
  by (rewrite <- R2; exact (KR (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite <- R3; exact (KR (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite <- R4; exact (KR (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T10 : getr (ms_regs ms) 10 = w64 (mv_c v + seg_spec.MC_READING))
  by (rewrite <- R10; exact (KR (10%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T11 : getr (ms_regs ms) 11 = w64 96)
  by (rewrite <- R11; exact (KR (11%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz F_s))
  by (rewrite <- R12; exact (KR (12%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
assert (T13 : getr (ms_regs ms) 13 = w64 lptr)
  by (rewrite <- R13; exact (KR (13%bv : bv 5) ltac:(repeat (first [left; reflexivity | right])))).
clear KR.
pose proof (aregs_preserved_of_st_ok SEGS (w_H Wc) E _ ms regs1 [] HS HAG ltac:(vm_compute; reflexivity)) as PRES.
prreg HS (1%bv : bv 5) P1.
assert (P1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_m_file + 0x15c))) by (rewrite P1; reflexivity).
clear P1.
pmkst HS.
(* the numbers of the call *)
unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *.
clear Hs1 Hs1m32 Hsp16 Hsegs R2 R3 R4 R10 R11 R12 R13.
pose proof HADDR as (Hq0 & Hq63 & _).
assert (UspT : spZ (ms_regs ms) = mf_s1 (mv_sp v)) by (unfold spZ; rewrite T2; apply mf_w64_u; lia).
assert (U13 : bv_unsigned (getr (ms_regs ms) 13) = lptr) by (rewrite T13; apply mf_w64_u; lia).
assert (Hsp' : spZ (ms_regs ms) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by lia.
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite P1'; apply ret_ok_codeptr_v; [unfold AF_m_file; lia | vm_compute; reflexivity]).
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K SegInstA.STK_m_file (mv_sp v)
  (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc
  (ms_mem ms) mdv 0 (ms_regs ms) (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp' Ho16 ltac:(lia) ltac:(lia) ltac:(lia)
  Hraw T3 T4) as (EPRE & ESTK & EPRES).
(* the mconf block: a live heap block, c->reading its last 96 bytes *)
destruct HHEAP as (b & m & Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARt Hin) as (_ & Hb4096 & Hbceil & _ & _ & _).
assert (Hr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
(* the text: snprintf writes min (|T|, 95) bytes and the NUL *)
pose proof HSTR as ((_ & HN0) & _).
destruct (mf_sn_bytes ltext HN0) as [SNB SNL].
destruct (mf_reading_bytes ltext HN0) as (_ & RBL & _).
assert (Hw : 1 <= RtPFShared.sn_len (96 - 1) ltext <= 96) by (rewrite SNL; lia).
(* the facts the contract reads at the call's memory, which is the step's (the run wrote no byte) *)
assert (HROM : RtDefs.rt_rom_view SEGS B Wc (ms_mem ms)).
{ intros a Hrom Ho He. rewrite EQV. exact (HROD a Hrom Ho He). }
destruct (SSP _ _ _ _ _ HARt) as (HG1 & cval & HG2).
pose proof (mfs_str_eq _ _ lptr ltext EQV HSTR) as HSTRt.
pose proof (mfs_addr_eq _ _ lptr _ EQV HADDR) as HADDRt.
pose proof (mfs_lit_eq SEGS B _ _ _ F_s EQV HLIT) as HLITt.
(* the destination *)
assert (Hdh : sa_heap B lyc Sc (mv_c v + 9140) (RtPFShared.sn_len (96 - 1) ltext))
  by (exists b, m; split; [exact Hin | lia]).
destruct (mf_dest_heap SEGS B LAWS lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (mv_c v + 9140)
  (RtPFShared.sn_len (96 - 1) ltext) pa_img_cover HARt Hdh ltac:(lia) ltac:(lia)) as (DOK & _ & Hoff0).
assert (Hoff : mfs_nam (mv_c v + 9140 + RtPFShared.sn_len (96 - 1) ltext <= 65536 \/ kImgEnd <= mv_c v + 9140))
  by exact Hoff0.
clear Hoff0.
(* the %s argument and the format *)
assert (HDJt : sa_disj lptr (seg_spec.cstr_span lptr ltext) (mv_c v + 9140) (RtPFShared.sn_len (96 - 1) ltext))
  by (unfold sa_disj in *; lia).
destruct (mf_label_arg SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv lptr (mv_c v + 9140) ltext RtPFCmd.CMD_SNP_K
  (spZ (ms_regs ms)) (RtPFShared.sn_len (96 - 1) ltext) HARt Hlp0 HSTRt HADDRt Hlen HLOC HDJt ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia)) as (ARG & SLK & AM8).
assert (FMT : RtPFShared.fmt_at (rdW Wc (ms_mem ms))
  (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms)) (mv_c v + 9140) (RtPFShared.sn_len (96 - 1) ltext))
  (SegInstA.seg_litA_fz F_s) F_s).
{ apply (mf_fmt_lit SEGS B lyc Sc Wc (ms_mem ms) mdv); [exact HARt | exact HLITt | lia | lia | lia | lia | exact Hoff]. }
pose proof (ASNPRINTF fx) as HA.
unfold asnprintf_realizes, RtPFCmd.asnprintf_sh, RtPFCmd.cmd_asnprintf_realizes in HA.
(* 0x86014: snprintf(c->reading, 96, "%s", text) writes the reading (the footprint's fifth range, the mconf block) *)
unfold MF_POST.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
    (fun a => mv_c v + 9140 <= a < mv_c v + 9140 + RtPFShared.sn_len (96 - 1) ltext)
    (SIGMA SS___interceptor_trampoline_snprintf) Wc (ms_regs ms) (ms_mem ms) SegInstA.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc
    mdv 0 (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + (AF_m_file + 0x15c))) _ HJ Hsp' Ho16 ltac:(lia)
    ltac:(lia) ltac:(lia) P1').
  - intros a Ha. right; left. split.
    + exists (mv_c v + seg_spec.MC_NKEPT, mv_c v + seg_spec.MC_READING + 96). split.
      * unfold M_FILE_FP. right; right; right; right; left. reflexivity.
      * cbn [fst snd]. unfold seg_spec.MC_NKEPT, seg_spec.MC_READING. lia.
    + exists b, m. split; [exact Hin | lia].
  - apply (srr_art_postF_of_pf SEGS B RtPFCmd.CMD_SNP_K lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv _ (mv_c v + 9140)
      (RtPFShared.sn_len (96 - 1) ltext) (RtPFShared.sn_bytes (96 - 1) ltext) (Z.of_nat (length ltext)) EPRES).
    apply (HA lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (mv_c v + 9140) 96 (SegInstA.seg_litA_fz F_s) []
      (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) ltext cval EPRE ESTK EPRES T10 T11 T12 HROM).
    + unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFCmd.CMD_SNP_CR, RtPFShared.snp_out. unfold mfs_nam, kImgEnd in Hoff. rewrite UspT.
      repeat (apply Forall_cons; [repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]); apply Forall_nil|]).
      apply Forall_nil.
    + exact HG1.
    + exact HG2.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold RtPFShared.snp_out. unfold mfs_nam, kImgEnd in Hoff. rewrite UspT.
      repeat (apply Forall_cons; [unfold zdisjoint, SegInstA.gotwA; cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFShared.snp_out. unfold mfs_nam, kImgEnd in Hoff. rewrite UspT.
      repeat (apply Forall_cons; [unfold zdisjoint, SegInstA.guardA; cbn [fst snd]; lia|]). apply Forall_nil.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length Z.of_nat]. lia.
    + unfold RtPFShared.snp_out. cbn [length Z.of_nat]. rewrite UspT.
      repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil.
    + (* the format family, by hand: "%s" and one string argument *)
      exists F_s, [RtPFPf.Ps], [RtPFPf.APtr ltext].
      split; [exact FMT|]. split; [exact mfs_parse|]. split; [apply RtPFCmd.pf_cmd_piece_all|].
      split.
      { cbn [map app RtPFShared.pf_args_asan]. rewrite mfs_argZ3, U13. exact (conj ARG I). }
      split; [exact (mfs_text ltext)|]. split; [exact I|].
      split; [unfold RtPFCmd.CMD_IMG_LO; rewrite mfs_fs_lit; lia|].
      split; [unfold RtPFCmd.CMD_GOTW; rewrite mfs_fs_lit, mfs_fs_len; lia|].
      split.
      { cbn [map app RtPFCmd.cmd_args_slack]. rewrite mfs_argZ3, U13, mf_str_end_span. exact (conj SLK I). }
      split; [intros Hf; pose proof mfs_fs_len as Hl; rewrite Hf in Hl; discriminate Hl|].
      cbn [map app RtPFCmd.cmd_args_amem]. rewrite mfs_argZ3, U13. exact (conj AM8 I).
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold RtPFShared.snp_out. cbn [pairwise]. rewrite UspT. split; [|split; [apply Forall_nil | exact I]].
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
    + exact DOK.
    + exact (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv b m (mv_c v + 9140)
        (RtPFShared.sn_len (96 - 1) ltext) HARt Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv b m); [exact HARt | exact Hin | lia | lia].
    + apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv b m);
        [exact HARt | exact Hin | lia | lia | lia].
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. unfold mfs_nam, kImgEnd in *. lia.
    + exact HFRM. }
(* back at 0x86018 at the FP state fx1 the wrapper returns *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (H10 & HBY) & HK2).
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin) as (_ & _ & _ & _ & Hbpres2 & _).
apply (HK fx1 regs2 mem2 md2 Hfx).
- intros r Hcs. rewrite (HP2 r Hcs). exact (PRES r Hcs).
- exact HJ2.
- intros i Hi. rewrite (HBY (Z.of_nat i)) by (rewrite SNL; lia). rewrite SNB, Nat2Z.id. reflexivity.
- intros i Hi. apply (aview_some_of_apresent SEGS).
  exact (proj1 (Hbpres2 (mv_c v + 9140 + Z.of_nat i) ltac:(lia))).
- intros a Ha Hn1 Hn2. rewrite (HK2 a Ha); [apply EQV | lia | lia].
Qed.
End e.
End f.
End d.

About mf_snp_step.
Print Assumptions mf_snp_step.
