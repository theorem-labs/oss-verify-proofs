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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 243 of its 289 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the entry segment of its walk, from
   the entry 0x8a218 (BASE + AF_reac_declared_vlan_split) to the point K1 0x8a278, after the strrchr wrapper. The
   image-A walk at commit ceb7e39832b2 has no file for this stretch; it is written for image B.
   0x8a218-0x8a238: the 64-byte frame, ra and s0 .. s6 saved; s2 = segment, s1 = parent, s3 = cap, s0 = vid.
   0x8a244, 0x8a24c, 0x8a254, 0x8a25c: the four `beqz` tests of segment, parent, cap and vid, each decided "not
   taken" by the run (vs_run1) from the seed facts of a0 .. a3 (segment, parent, vid in [4096, 2^47 - 1], cap = 16;
   split_pre through vs_seed). 0x8a260-0x8a268: the GOT word 0xa3210 (listing object 0) holds the shadow-base cell
   0xac7b8 (object 12), whose word, the shadow base, goes to s6 (PALib). 0x8a26c-0x8a274: a1 = 46, a0 = segment, the
   call of the strrchr wrapper (trampoline 0x43ab8) through RtSeg.astrrchr_realizes, its premises from split_pre
   (sa_str, sa_addr, the band room, sa_loc) and arodata_okP, all kept by the frame stores, which lie in
   [sp0 - 64, sp0). Its answer (the last dot or 0) is SegModel.strrchr's (vs0_strrchr_none, vs0_strrchr_at).
   This stretch has no instrumented check, no call of an error path and no branch to the UBSan trap `unimp`
   0x8a3d8. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* SegModel.strrchr against the wrapper's answer: no c in the text, or c last at j *)
Lemma vs0_last_idx_none : forall c l i acc, ~ In c l -> SegModel.last_idx c l i acc = acc.
Proof.
induction l as [|b l IH]; intros i acc Hn; cbn [SegModel.last_idx]; [reflexivity|].
destruct (Z.eqb_spec b c) as [->|Hb]; [exfalso; apply Hn; left; reflexivity|].
apply IH. intros H. apply Hn. right. exact H.
Qed.
Lemma vs0_last_idx_at : forall c l j i acc, RtSeg.last_at l c j -> SegModel.last_idx c l i acc = Some (i + j)%nat.
Proof.
induction l as [|b l IH]; intros j i acc (Hj & Hn & Hs); cbn [length] in Hj; [lia|].
cbn [SegModel.last_idx].
destruct j as [|j].
- cbn [nth] in Hn. subst b. rewrite Z.eqb_refl. cbn [skipn] in Hs.
  rewrite (vs0_last_idx_none c l (S i) (Some i) Hs). f_equal. lia.
- cbn [nth skipn] in Hn, Hs.
  assert (Hl : RtSeg.last_at l c j) by (split; [lia | split; [exact Hn | exact Hs]]).
  rewrite (IH j (S i) _ Hl). f_equal. lia.
Qed.
Lemma vs0_strrchr_none : forall s, SegModel.nulfree s -> ~ In 46 s -> SegModel.strrchr s 46 = None.
Proof. intros s Hn Hi. unfold SegModel.strrchr. rewrite (SegModel.cut_nul_id s Hn). apply vs0_last_idx_none. exact Hi. Qed.
Lemma vs0_strrchr_at : forall s j, SegModel.nulfree s -> RtSeg.last_at s 46 j -> SegModel.strrchr s 46 = Some j.
Proof. intros s j Hn Hl. unfold SegModel.strrchr. rewrite (SegModel.cut_nul_id s Hn). exact (vs0_last_idx_at 46 s j 0 None Hl). Qed.

(* a register of acallee_saved, by its literal *)
Ltac vs0_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    replace (bv_unsigned x) with v by (vm_compute; reflexivity) end;
  lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a register of the symbolic state at a call *)
Lemma vs0_reg : forall E ss (ms : machine_state) (H : word -> bool) (r : bv 5) t,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = t -> getr (ms_regs ms) r = sv_denot E t.
Proof using. intros E ss ms H r t HS Ht. rewrite <- Ht. exact (st_ok_restrict_reg SEGS H E ss ms r HS). Qed.
Lemma vs0_reg_atom : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) n (r r' : bv 5),
  st_ok SEGS E ss (restrict H ms) -> ew E n = getr regs r' ->
  sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = getr regs r'.
Proof using.
intros E ss ms H regs n r r' HS Hn Hs. rewrite (vs0_reg E ss ms H r _ HS Hs).
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* a saved word of the frame, read from the symbolic state's stack region *)
Lemma vs0_slot : forall E H (mem : word -> option byte) rg off n (r : bv 5) (regs : bvmap 5 word) sp,
  region_ok SEGS E (mrestrict H mem) rg -> base_val E (YP09.r_base rg) = sp ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks rg) ->
  ew E n = getr regs r ->
  rdword (aview SEGS H mem) (sp + off) = Some (bv_unsigned (getr regs r)).
Proof using.
intros E H mem rg off n r regs sp Hr Hb Hin Hn.
pose proof (region_ok_chunk SEGS E _ rg _ Hr Hin) as Hc. rewrite Hb in Hc.
pose proof (bv_unsigned_in_range 64 (getr regs r)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
apply rdword_of_val_mem; [|exact R].
refine (val_of_chunk_ok SEGS E _ sp off 8 (SOff n 0) (bv_unsigned (getr regs r)) Hc _ _ ltac:(cbn; lia)).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact R.
Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis STRRCHR : forall fx0 : YK11.FPState, @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis TL : PALib B.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* where the segment lies: a heap block, a side-stack frame or the image, all below the allocator's ceiling *)
Lemma vs0_loc : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR HL Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B4 & Bc & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Q]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & _). lia.
- destruct (HI q ltac:(lia)) as (I1 & _). destruct (HI (q + n - 1) ltac:(lia)) as (I2 & _).
  pose proof (pa_img_range _ I1). pose proof (pa_segs_low _ I2). lia.
Qed.

(* the strrchr wrapper's answer on the segment, and the presence it keeps *)
Definition vs0_Q (e : vsE) (memT : word -> option byte) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs' mem' =>
  ((getr regs' 10 = w64 0 /\ ~ In 46 (map (fun b : byte => bv_unsigned b) (seg_spec.zb (e_s e)))) \/
   (exists j, RtSeg.last_at (map (fun b : byte => bv_unsigned b) (seg_spec.zb (e_s e))) 46 j /\
      getr regs' 10 = w64 (e_seg e + Z.of_nat j))) /\
  (forall a, apresent (w_H (e_W e)) memT a -> apresent (w_H (e_W e)) mem' a).

Lemma vs_K0 : vs_K1_stmt B gotw guard -> forall e, vs_entry B gotw guard e ->
  vs_goal B e (e_W e) (cfg_at SEGS (BASE + AF_reac_declared_vlan_split) (e_regs e) (e_mem e) (e_md e)).
Proof using STRRCHR TL.
intros HK1 e HE.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : VS_STK = 12352) by reflexivity.
assert (HE4 : ESTACK = 4096) by reflexivity.
assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
assert (P40 : 2 ^ 40 = 1099511627776) by reflexivity.
assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
(* where the three objects lie (sa_loc for the segment, sa_dst for parent and the vid cell) *)
destruct (vs0_loc _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as (Sg4 & Sgc).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & _).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 2 HAR Hstk ltac:(lia) Hvdst) as (Vlo & Vhi & _).
(* the segment as the wrapper's byte list *)
destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (HB & HN & HZS).
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
assert (Hzb : length (seg_spec.zb (e_s e)) = length (e_s e)) by apply length_map.
(* the seeded entry state and the journal from the entry *)
pose proof (vs_seed B LAWS TL (e_W e) (e_regs e) (e_mem e) (e_ly e) (e_S e) (e_md e) (e_ch e) (e_seg e) (e_parent e) (e_vid e)
  HPRE H10 ltac:(lia) H11 ltac:(lia) H12 H13 ltac:(lia) Hv2) as HS.
set (E := Eimg (Ereg (e_regs e) vs_extra0)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (e_regs e) r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply vs_E32).
assert (Usp : bv_unsigned (ew E 2) = spZ (e_regs e)) by (rewrite (EV 2%nat 2%bv eq_refl); reflexivity).
pose proof (ajournal_init SEGS B VS_STK (e_FP e) (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) HPRE) as HJ.
unfold vs_goal, cfg_at.
change (w64 (BASE + AF_reac_declared_vlan_split)) with (Z_to_bv 64 (BASE + AF_reac_declared_vlan_split)).
(* 0x8a218 .. 0x8a270: the frame, the four beqz (not taken: the seed facts of a0 .. a3), s6 = the shadow base,
   a1 = 46, a0 = segment; the run stops at the call 0x8a274 (vs_run1) *)
eapply (RUNC (e_W e) FUEL E vs_ss0 vs_ss1 SS___interceptor_trampoline_strrchr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS vs_run1 HJ).
{ awr_ok_tac. exact Usp. }
intros ms1 mat HS1 HJ1 HF HFr HG. cbn [ms_mem mkst] in HF, HFr, HG, HJ1. clear HF.
(* the run wrote only its frame [sp0 - 64, sp0) *)
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - 64 <= a < spZ (e_regs e)) ->
  rdW (e_W e) (ms_mem ms1) a = rdW (e_W e) (e_mem e) a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H (e_W e)) (e_mem e) (ms_mem ms1)
    (fun a => spZ (e_regs e) - 64 <= a < spZ (e_regs e)) HFr).
  intros b wlo whi a Hin Hrr.
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in replace l with l' in Hin by (vm_compute; reflexivity) end.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; cbv beta; lia|]).
  destruct Hin. }
(* the registers at the call *)
pose proof (vs0_reg E _ ms1 _ 2%bv (SOff 2 (-64)) HS1 ltac:(vm_compute; reflexivity)) as R2.
cbn [sv_denot] in R2. rewrite Usp in R2.
pose proof (vs0_reg E _ ms1 _ 1%bv (SOff A_TEXT 21688) HS1 ltac:(vm_compute; reflexivity)) as R1.
rewrite (codeptr_val E 21688 HEI) in R1.
pose proof (vs0_reg E _ ms1 _ 11%bv (SLit 46) HS1 ltac:(vm_compute; reflexivity)) as R11.
cbn [sv_denot] in R11.
pose proof (vs0_reg E _ ms1 _ 22%bv (SOff 32 0) HS1 ltac:(vm_compute; reflexivity)) as R22.
cbn [sv_denot] in R22. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in R22.
assert (R3 : getr (ms_regs ms1) 3 = getr (e_regs e) 3)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 3%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R4 : getr (ms_regs ms1) 4 = getr (e_regs e) 4)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 4%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R8 : getr (ms_regs ms1) 8 = getr (e_regs e) 13)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 13%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R9 : getr (ms_regs ms1) 9 = getr (e_regs e) 11)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 11%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R10 : getr (ms_regs ms1) 10 = getr (e_regs e) 10)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 10%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R18 : getr (ms_regs ms1) 18 = getr (e_regs e) 10)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 10%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R19 : getr (ms_regs ms1) 19 = getr (e_regs e) 12)
  by (eapply (vs0_reg_atom E _ ms1 _ (e_regs e) 12%nat); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity]).
assert (R27 : forall r, 23 <= r <= 27 -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr (e_regs e) (Z_to_bv 5 r)).
{ intros r Hr. assert (Hc : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [-> | Hc]); try subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let n := eval compute in (Z.to_nat k) in
    eapply (vs0_reg_atom E _ ms1 _ (e_regs e) n); [exact HS1 | apply EV; reflexivity | vm_compute; reflexivity] end. }
assert (Hsp1 : spZ (ms_regs ms1) = spZ (e_regs e) + -64).
{ unfold spZ at 1. rewrite R2. apply unsigned_lit_small. lia. }
(* the frame's saved words at the call, from the stack region of the symbolic state *)
lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let rg := eval vm_compute in (nth 0 (ss_mem ss) (stack_region 0)) in
  pose proof (st_ok_region_nth E ss _ 0 rg HS1 ltac:(vm_compute; reflexivity)) as Rst end.
cbn [ms_mem restrict] in Rst.
(* 0x8a274: the strrchr wrapper *)
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
  (e_ly e) (e_S e) (e_W e) (ms_mem ms1) _ 0 (ms_regs ms1) (-64) HJ1 Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hraw
  ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)) as HPRE1.
pmkst HS1.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strrchr)
    (e_W e) (ms_regs ms1) (ms_mem ms1) VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) _ 0 (-64) _ (vs0_Q e (ms_mem ms1)) HJ1).
  1: exact Hsp1. 1: reflexivity. 1: lia. 1: lia. 1: lia. 1: exact R1. 1: intros a [].
  eapply SRr_mono.
  { apply (STRRCHR fx (e_ly e) (e_S e) (e_W e) (ms_regs ms1) (ms_mem ms1) _ (e_seg e) 46 (seg_spec.zb (e_s e))).
    - exact HPRE1.
    - rewrite R10. exact H10.
    - rewrite R11. reflexivity.
    - lia.
    - lia.
    - (* the segment's bytes and NUL (sa_str), kept by the frame stores *)
      split; [|exact HN]. intros i Hi.
      assert (Hi2 : (i < length (e_s e) + 1)%nat) by (rewrite length_app, Hzb in Hi; cbn [length] in Hi; lia).
      rewrite (KO (e_seg e + Z.of_nat i)) by lia. exact (HB i Hi).
    - (* the read of length s + 1 bytes: sa_addr, the bytes of sa_str, below the wrapper's window *)
      unfold aread_ok, astr_len. rewrite Hzb.
      pose proof Hsadd as (Sa0 & Sa63 & Samr & Sara & Sahv).
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - rewrite (KO a) by lia. destruct Hstr as ((Hzs & _) & _).
          pose proof (Hzs (Z.to_nat (a - e_seg e)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
          rewrite Z2Nat.id in Hb by lia. replace (e_seg e + (a - e_seg e)) with a in Hb by lia. rewrite Hb. discriminate.
        - unfold ascratch_stk. rewrite Hsp1. lia. }
      split; [exact Samr|]. split.
      + eapply range_addressable_kept_win; [exact KO | lia | lia | lia | exact Sara].
      + intros Hn. eapply shadow_hull_vis_kept_win; [exact KO | lia | lia | lia | exact Hn | exact (Sahv Hn)].
    - (* the band room past the NUL (split_pre) *)
      unfold astr_len. rewrite Hzb. exact Hamr.
    - (* the slack to the word's end (sa_tail) *)
      unfold astr_len. rewrite Hzb. intros a Ha.
      pose proof (Z.mod_pos_bound (e_seg e + Z.of_nat (length (e_s e))) 8 ltac:(lia)).
      rewrite (KO a) by lia. exact (proj2 Hstr a Ha).
    - (* the read-only bytes the wrapper reads (arodata_okP) *)
      intros a Hr Ho He.
      assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
      pose proof (pa_segs_low _ Hi). rewrite (KO a) by lia. exact (HROD a (or_introl Hr) Ho He). }
  intros W' c' _ (HW & regs' & mem' & md' & Hc & HAR' & HP' & Hsb & HQ & Hk & Hpr & Hsc).
  split; [exact HW|]. exists regs', mem', md'.
  split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsb|].
  split; [split; [exact HQ | exact Hpr]|]. split; [exact Hk|]. split; [exact Hpr | exact Hsc]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQ2 & Hpr2) & HFR2').
pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x : False => x)) as HFR2. clear HFR2'.
assert (G : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r).
{ intros r Hr. specialize (HP2 (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in HP2. exact HP2. }
(* the state at K1 *)
assert (SLT : forall rg0 off n (r : bv 5), region_ok SEGS E (mrestrict (w_H (e_W e)) (ms_mem ms1)) rg0 ->
  YP09.r_base rg0 = Some 2%nat -> -64 <= off -> off + 8 <= 0 ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks rg0) -> Z.of_nat n = bv_unsigned r ->
  rdword (rdW (e_W e) mem2) (spZ (e_regs e) + off) = Some (bv_unsigned (getr (e_regs e) r))).
{ intros rg0 off n r Hr0 Hb0 Ho1 Ho2 Hin Hn.
  rewrite <- (vs0_slot E _ _ rg0 off n r (e_regs e) (spZ (e_regs e)) Hr0 ltac:(rewrite Hb0; exact Usp) Hin (EV n r Hn)).
  apply rdword_ext. intros k Hk. apply HFR2; lia. }
assert (HSL : vs_slots (rdW (e_W e) mem2) (e_sp e) (e_regs e)).
{ unfold e_sp. intros i r Hr.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error vs_saved] in Hr; [..| destruct i; discriminate Hr];
  injection Hr as <-;
  lazymatch goal with |- rdword _ (?sp - 8 - 8 * Z.of_nat ?k) = Some (bv_unsigned (getr _ ?r)) =>
    let off := eval vm_compute in (- 8 - 8 * Z.of_nat k) in
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    replace (sp - 8 - 8 * Z.of_nat k) with (sp + off) by lia;
    apply (SLT _ off n r Rst eq_refl); [lia | lia | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | reflexivity] end. }
assert (HR : vs_regs e regs2).
{ unfold vs_regs, e_sp.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - change (spZ regs2) with (bv_unsigned (getr regs2 2)). rewrite (G 2%bv) by vs0_cs.
    change (bv_unsigned (getr (ms_regs ms1) 2)) with (spZ (ms_regs ms1)). lia.
  - rewrite (G 3%bv) by vs0_cs. exact R3.
  - rewrite (G 4%bv) by vs0_cs. exact R4.
  - rewrite (G 8%bv) by vs0_cs. rewrite R8. exact H13.
  - rewrite (G 9%bv) by vs0_cs. rewrite R9. exact H11.
  - rewrite (G 18%bv) by vs0_cs. rewrite R18. exact H10.
  - rewrite (G 19%bv) by vs0_cs. rewrite R19. exact H12.
  - rewrite (G 22%bv) by vs0_cs. exact R22.
  - intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (R27 r Hr). }
assert (Hctx : vs_ctx0 B e regs2 mem2 md2).
{ unfold vs_ctx0, vs_ctxW. split; [exact HJ2|]. split; [exact HR|]. split; [exact HSL|]. split.
  - intros a Ha Hw _. unfold e_sp in Hw. rewrite (HFR2 a Ha ltac:(lia)). exact (KO a Ha ltac:(lia)).
  - intros a Ha. apply Hpr2. eapply apresent_grows; [exact HG | exact Ha]. }
(* K1: a0 = 0 and no dot, or a0 = segment + di with di the last dot *)
assert (Hzs : map (fun b : byte => bv_unsigned b) (seg_spec.zb (e_s e)) = e_s e) by exact HZS.
rewrite Hzs in HQ2.
destruct HQ2 as [(Hz & Hni) | (j & Hj & Hrj)].
- exact (HK1 e regs2 mem2 md2 0 HE Hctx Hz (or_introl (conj eq_refl (vs0_strrchr_none _ Hnul Hni)))).
- exact (HK1 e regs2 mem2 md2 (e_seg e + Z.of_nat j) HE Hctx Hrj
    (or_intror (ex_intro _ j (conj (vs0_strrchr_at _ _ Hnul Hj) eq_refl)))).
Qed.
End e.
End f.
End d.
