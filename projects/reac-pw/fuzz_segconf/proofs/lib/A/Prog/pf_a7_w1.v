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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 824 of its 867 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_b.v, with its module paths and module names changed; 598 of its 666 lines of code are new or changed and 799 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the HEADER piece of segment A7 of
   reac_segconf_parse_file's walk (2026-10-30):

     a7_w1 : A7_S_HDR B        (pf_a7_m.v)
           = forall f0 n, HA_FUN B n -> HA_CLOSE B n -> H_HDR (fx := f0) B n

   HDR 0x87f6c -> CLOSE 0x880ac, or -> the funnel FUN 0x88064 through the refuse call at 0x88060.
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s): 20
   instructions on the two paths, plus the 3 of check 8's slow arm, 23 walked in all:
     0x87f6c addi a1, zero, 0x5d (']')   0x87f70 mv a0, s7 (= lp, the trimmed line)
     0x87f74 jal <wrapper_strchr>                      -- a0 = the ']' or 0
     0x87f78 beqz a0, 0x8804c                          -- not closed
     0x87f7c addi a1, a0, 1  0x87f80 srli a2, a1, 3  0x87f84 add a2, a2, s6  0x87f88 lb a2, 0(a2)
     0x87f8c bnez a2, 0x88a28                          -- inline check 8, with its slow arm 0x88a28-0x88a30
     0x87f90 lbu a1, 0(a1)   0x87f94 beqz a1, 0x880ac  -- nothing after the ']' -> CLOSE
     0x87f98 auipc a0 / 0x87f9c addi a2, a0, 0x4a8 (= seg_litA_rc F_after)   0x87fa0 j 0x88054
     0x8804c auipc a0 / 0x88050 addi a2, a0, 0x3b4 (= seg_litA_rc F_notclosed)
     0x88054 mv a0, s8 (c)  0x88058 mv a1, s10 (lineno)  0x8805c mv a3, s7 (lp)
     0x88060 jal <refuse>                              -- returns at 0x88064 = FUN
   The error arm 0x88d00 of check 8 is not reached: the token executor decides the check from the shadow
   entry of the byte at lp + ci + 1, which is a byte of buf (pf_a7_d.v a7_addr_buf).

   THE SHAPE. Three token runs (lib/A/Prog/SegPaLib.v paj_run_tok), each from a seed of its own built with
   pa_entry_st_ok_full, as trim_t.v's tf_entry and pf_a7_q.v's a7_seed are:
     w1_seed0  at HDR, and at strchr's return on the NOT-FOUND arm: no region and no fact, because the run
               touches no memory;
     the FOUND arm's seed (inside w1_cl): one read-only region, the byte of buf at a0 + 1 over the fresh
               atom 32, the three facts the token logic needs (a0 a pointer, s6 the shadow base, the byte in
               [0, 256)) and the shadow entry w1_SHF = [mkSHE 10 1 2], whose range_addressable is a7_addr_buf.
   pf_a7_q.v's a7_seed is NOT used here: this piece reads no slot, no saved register and no shadow cell of
   the frame, so its four regions are not needed, and buf's region would overlap the byte's.
   The strchr call is stepped by PaArt.v's aj_art_at with pf_a7_r.v's premise bundle a7_strchr_pre_87f74;
   the refuse call by PaFx.v's cl_callSF (refuse returns at another FP state) with pf_a7_s.v's closed call
   site a7_refuse_site_88060, and the cut's facts are rebuilt after it by pf_a6_k.v's a6_keeps_refuse /
   a6_base_move / a6_nm_move, exactly as pf_a7_u.v does at 0x880f8. After strchr the rebuild is pf_a5_k.v's
   a5_move0 (no Section hypothesis): an art_post entry keeps every byte outside its own window
   [s1 - 2 * ESTACK, s1), which lies inside A5's write set.
   The functional arms are pf_a7_f.v's a7_hdr_notclosed and a7_hdr_after; the CLOSE arm hands INV_CLOSE the
   two facts strchr and the byte give: strchr (pf_tline s o) RBR = Some ci and nth (S ci) (pf_tline s o) 0 = 0.

   SECTION HYPOTHESES (and the step that forces each):
     ASTRCHR  the strchr interceptor, the interceptor owner's row 6 at the listing's trampoline (the call at 0x87f74)
     REF      refuse_contract at image A's numbers (the call at 0x88060)
     SIGP     seg_sig_prog, to read the listing's call target of refuse as BASE + AF_refuse
     OBJ      seg_val_objs, for the two formats the auipc / addi pairs form (A_OBJ 38 = F_after at 0x87f98,
              A_OBJ 39 = F_notclosed at 0x8804c)
     TL       PALib B, for aj_art_at's errno cell (api_env), as trim.v takes it
     VRO, SSPX  forced ONLY by pf_a6_k.v's a6_base_move, the rebuild AFTER the refuse call: refuse's post
              gives only its journal, which keeps an image byte only when it is not an owned static, and
              arodata_okP there needs pa_relro_img. Both are discharged by listing stage 2
             (SegRecCells.seg_rec_cells, after AF0m), in reac_segconf_parse.v:137's shape.
   Nothing else: sa_ssp, arodata_okP and rt_rom_view before the refuse call and across the strchr call come
   out of pf_base itself (pf_a5_k's a5_keep_obj0 inside a5_move0, pf_a7_r's a7_rom). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_m pf_a7_q pf_a7_r pf_a7_s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* no Zify euclidean-division override here: the stack-window side conditions of cl_callSF need lia to use
   the `mod` facts of the realigned sp (pf_a7_u.v does the same) *)
Open Scope bv_scope.
Open Scope Z_scope.

(** ** strchr's return, as a listing offset (BASE + AF = 0x87a78) *)
Definition W1_RET : Z := AF_reac_segconf_parse_file + 0x500.   (* 0x87f78 *)

(** ** Pure: strchr against the interceptor's answer (RtSeg.first_at) *)
Lemma w1_memchr_none : forall (l : list Z) (c : Z), ~ In c l -> memchr l c = None.
Proof.
  induction l as [|a l IH]; intros c Hn; cbn [memchr]; [reflexivity|].
  destruct (Z.eqb_spec a c) as [->|Hne]; [exfalso; apply Hn; left; reflexivity|].
  rewrite (IH c ltac:(intros H; apply Hn; right; exact H)). reflexivity.
Qed.

Lemma w1_memchr_first : forall (l : list Z) (c : Z) (j : nat), RtSeg.first_at l c j -> memchr l c = Some j.
Proof.
  induction l as [|a l IH]; intros c j (Hj & Hnth & Hnin); cbn [length] in Hj; [lia|].
  destruct j as [|k]; cbn [memchr].
  - cbn [nth] in Hnth. subst a. rewrite Z.eqb_refl. reflexivity.
  - cbn [nth] in Hnth. cbn [firstn In] in Hnin.
    destruct (Z.eqb_spec a c) as [->|Hne]; [exfalso; apply Hnin; left; reflexivity|].
    rewrite (IH c k); [reflexivity|].
    split; [cbn [length] in Hj; lia|]. split; [exact Hnth|].
    intros H. apply Hnin. right. exact H.
Qed.

Lemma w1_strchr_none : forall (l : list Z) (c : Z), nulfree l -> c <> 0 -> ~ In c l -> strchr l c = None.
Proof.
  intros l c Hn Hc Hin. rewrite (strchr_memchr l c Hn Hc). exact (w1_memchr_none l c Hin).
Qed.

Lemma w1_strchr_first : forall (l : list Z) (c : Z) (j : nat),
  nulfree l -> c <> 0 -> RtSeg.first_at l c j -> strchr l c = Some j.
Proof.
  intros l c j Hn Hc Hf. rewrite (strchr_memchr l c Hn Hc). exact (w1_memchr_first l c j Hf).
Qed.

(** r_trim's result holds no NUL (pf_a7_f.v a7_body_nul, for any argument) *)
Lemma w1_trim_nul : forall l : list Z, ~ In 0 (r_trim l).
Proof.
  intros l. unfold r_trim. cbv zeta.
  exact (nulfree_firstn _ _ (nulfree_dropwhile _ _ (cut_nul_nulfree _))).
Qed.

Lemma w1_nth_app0 : forall (l : list Z) (i : nat), (i <= length l)%nat -> nth i (l ++ [0]) 0 = nth i l 0.
Proof.
  intros l i Hi. destruct (Nat.lt_ge_cases i (length l)) as [H|H]; [apply app_nth1; exact H|].
  assert (i = length l) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.

(* a branch on an atom against zero (trim_t.v tr_br_eq0) *)
Lemma w1_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
  intros E n v b H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.

(** ** The symbolic states of the runs *)
(* HDR -> the strchr call, and strchr's return on the NOT-FOUND arm: the run touches no memory *)
Definition w1_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* the FOUND arm: the byte of buf at a0 + 1 on the fresh atom 32, read-only *)
Definition w1_rB : YP09.region := YP09.mkRegion (Some 10%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition w1_GF : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (22%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)] [] [].
Definition w1_ssF : sstate := mkSS W1_RET sr_atoms [w1_rB] None w1_GF.
Definition w1_SHF : list shent := [mkSHE 10 1 2].

(* a reader reads an address modulo 2 ^ 64 (the same lemma as pf_a7_w3_c.v's w3_view_wrap) *)
Lemma w1_view_wrap : forall segs H mem a, aview segs H mem a = aview segs H mem (a mod 2 ^ 64).
Proof.
  intros segs H mem a. unfold aview, mbyte.
  replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity.
Qed.

(* the run writes nothing: no region of w1_ss0 / w1_ssF has a write window (pf_a7_cr.v a7c_awr) *)
Local Ltac w1_awr :=
  try unfold w1_ssF; try unfold w1_ss0; cbn [ss_mem add_cond];
  repeat (apply awr_ok_cons_ro; [try unfold w1_rB; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil.

(* the run wrote nothing: no region has a write window (pf_a7_cr.v a7c_mem) *)
Local Ltac w1_same HF Hname msx memx :=
  assert (Hname : ms_mem msx = memx);
  [ apply functional_extensionality; intros xx; unfold frame_of in HF; rewrite HF; [reflexivity|];
    intros (rr & Hrr & Haa); cbn [ss_mem add_cond In] in Hrr;
    repeat (destruct Hrr as [<- | Hrr];
      [ try unfold w1_rB in Haa; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Haa; lia |]);
    destruct Hrr
  | ].

(* a token run extends the environment above its atom bound; the seed's agreement survives *)
Lemma w1_agree_ewset : forall k E E' m v, env_agree k E E' -> (k <= m)%nat -> env_agree k E (ewset E' m v).
Proof.
  intros k E E' m v (H1 & H2) Hk. split.
  - intros n Hn. rewrite ew_ewset_other by lia. exact (H1 n Hn).
  - rewrite ed_ewset. exact H2.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The environment: the registers, and the byte of the FOUND arm as atom 32 *)
Definition w1_E (rX : bvmap 5 word) (bz : Z) : env := Eimg (Ereg rX [Z_to_bv 64 bz]).

Lemma w1_E_img : forall rX bz, img_env VAL A_LIM (w1_E rX bz).
Proof. intros rX bz. unfold w1_E. apply Eimg_env. Qed.

Lemma w1_E_agree : forall rX bz, env_agree 32 (Ereg rX [Z_to_bv 64 bz]) (w1_E rX bz).
Proof.
  intros rX bz. split; [|reflexivity]. intros n Hn. unfold w1_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.

(* the seed's register agreement, at whatever environment the run left (tokens extend it above 1023) *)
Local Ltac w1_ag HS rX ex Hname :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (Hname : env_agree 32 (Ereg rX ex) Ex)
        by (repeat (apply w1_agree_ewset; [|lia]); apply w1_E_agree)
  | st_ok _ ?Ex _ _ =>
      assert (Hname : env_agree 32 (Ereg rX ex) Ex)
        by (repeat (apply w1_agree_ewset; [|lia]); apply w1_E_agree)
  end.

Lemma w1_ew_reg : forall rX bz k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (w1_E rX bz) k = getr rX r.
Proof. intros rX bz k r Hk. unfold w1_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.

Lemma w1_ew_bz : forall rX bz, ew (w1_E rX bz) 32 = Z_to_bv 64 bz.
Proof.
  intros rX bz. unfold w1_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra rX [Z_to_bv 64 bz] 0).
Qed.

Section q.
Context {fx : YK11.FPState}.
(** ** The seed with no region *)
Lemma w1_seed0 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc pc bz,
  st_ok_pi SEGS VAL (w1_E rX bz) (w1_ss0 pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
  intros Wc rX memc pc bz.
  rewrite restrict_mkst_fx. unfold w1_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - split; [exact I | split; exact I].
Qed.
End q.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the record hypothesis: the image's runtime cells a walk reads (SegPaLib.v PALib), as trim.v takes it;
   aj_art_at asks its errno cell (api_env) *)
Hypothesis TL : PALib B.
(* the listing's facts over the walk's abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after the refuse call, used nowhere else (see the head comment) *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
(* the interceptor owner's row 6, at the listing's strchr trampoline *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
(* refuse's contract at image A's numbers; it returns at another FP state *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Let errno_low := pal_env B TL.

(** ** The two formats the auipc / addi pairs form (pf_a7_u.v a7u_lit) *)
Lemma w1_lit_after : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 38) = w64 (seg_litA_rc F_after).
Proof.
  intros E HE. rewrite (img_env_atomP E (A_OBJ 38) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (OBJ 38%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Lemma w1_lit_notclosed : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 39) = w64 (seg_litA_rc F_notclosed).
Proof.
  intros E HE. rewrite (img_env_atomP E (A_OBJ 39) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (OBJ 39%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(** ** pf_base at another register bank and model (only the journal and pf_fi's register list move) *)
Lemma w1_base_regs : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX rX' memc mdc mdc' sc,
  pf_base (fx := fx1) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_rg rX' (a5_FI B v) ->
  pf_base (fx := fx1) B v pos lyc Sc Wc rX' memc mdc' sc.
Proof.
  intros fx1 v pos lyc Sc Wc rX rX' memc mdc mdc' sc
    (HCX & (_ & Hly & Hfs & Hperm & Hsaved & Hflag & Hfrm & _) & HOBJ & HSL & HFSH) HJ HRG.
  split; [exact HCX|].
  split; [exact (conj HJ (conj Hly (conj Hfs (conj Hperm (conj Hsaved (conj Hflag (conj Hfrm HRG)))))))|].
  exact (conj HOBJ (conj HSL HFSH)).
Qed.

Section x.
Context {fx : YK11.FPState}.

(** ** The refuse call at 0x88060, shared by the two arms (pf_a7_u.v's route at 0x880f8) *)
Lemma w1_ref : forall n, HA_FUN B n ->
  forall v pos lyc Sc Wc (rg : bvmap 5 word) memc mdc cf cur nm o ln d lp f,
  pf_base B v pos lyc Sc Wc rg memc mdc PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) ->
  pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) ->
  (f = F_notclosed \/ f = F_after) ->
  pf_rg rg (PF_RL v pos ++ PF_RM v o ln) ->
  getr rg 10 = w64 (p_c v) -> getr rg 11 = w64 (ln + 1) -> getr rg 12 = w64 (seg_litA_rc f) ->
  getr rg 13 = w64 lp -> getr rg 1 = Z_to_bv 64 (BASE + A7_FUN) ->
  SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (SIG SS_refuse)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (refuse cf (ln + 1) f [AS (pf_tline (p_s v) o)], None, nm) o ln).
Proof.
  intros n HFUN v pos lyc Sc Wc rg memc mdc cf cur nm o ln d lp f HB HMID HST HSTR HINB Hf HRG
    R10 R11 R12 R13 R1.
  pose proof (a7_st_of_base B v pos lyc Sc Wc rg memc mdc HB) as HST7.
  pose proof (a5_geo B v pos lyc Sc Wc rg memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof (a5_fi_regs B v pos lyc Sc Wc rg memc mdc PF_SC_LINE HB) as HFI.
  destruct (a5_chain B v pos lyc Sc Wc rg memc mdc PF_SC_LINE HB) as [ch1 HCH].
  pose proof HB as (HCX & (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
  pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
  pose proof HST as (HRC & HCUR & HNM & HCNT).
  pose proof HMID as (Ho & _ & _).
  pose proof STK_values as (_ & SRF & _ & SPF & _).
  pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
  assert (C2 : getr rg 2 = w64 (pf_s1 v)) by exact (a5_rg_get rg _ 2 _ HFI ltac:(cbn [a5_FI In]; tauto)).
  assert (C3 : getr rg 3 = w64 (as_gp B)) by exact (a5_rg_get rg _ 3 _ HFI ltac:(cbn [a5_FI In]; tauto)).
  assert (C4 : getr rg 4 = w64 (as_tp B)) by exact (a5_rg_get rg _ 4 _ HFI ltac:(cbn [a5_FI In]; tauto)).
  assert (C8 : getr rg 8 = w64 (pf_sp0 v)) by exact (a5_rg_get rg _ 8 _ HFI ltac:(cbn [a5_FI In]; tauto)).
  assert (Csp : spZ rg = pf_s1 v)
    by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  (* VERIFY rule 1j-bis at 0x88060: refuse_contract's premises besides afn_pre *)
  pose proof (a7_refuse_site_88060 B v pos lyc Sc Wc memc mdc rg cf o ln d n lp f HST7 HRC
    (a7_cnt_zero cf (p_s v) o Ho HCNT) HMID HFRM Hf R10 R11 R12 R13 HSTR HINB)
    as (ROD & _ & Hc64 & _ & Hl64 & _ & Hf64 & RPRE & ROOM & EV).
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callSF (fx := fx) B LAWS Wc rg memc _ STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A7_FUN)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) f [AS (pf_tline (p_s v) o)]) /\
         sa_noalloc B lyc Sc ly2 S2) HJ).
    - rewrite Csp. lia.
    - exact S1d.
    - lia.
    - rewrite SRF. lia.
    - rewrite SRF, SPF. lia.
    - exact C3.
    - exact C4.
    - exact R1.
    - apply ret_ok_codeptr_v; [unfold A7_FUN, AF_reac_segconf_parse_file; lia | reflexivity].
    - rewrite unsigned_lit_small by (unfold A7_FUN, AF_reac_segconf_parse_file; lia).
      unfold A7_FUN, AF_reac_segconf_parse_file. lia.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
    - intros HPRE1. eapply SRr_mono.
      { exact (REF fx lyc Sc Wc rg memc mdc ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1) cf f
          [AS (pf_tline (p_s v) o)] HPRE1 ROD R10 Hc64 R11 Hl64 R12 Hf64 RPRE ROOM EV). }
      cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hg1 & Hg2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
      split; [exact Hg1|]. split; [exact Hg2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
      apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
      unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
  (* back at 0x88064 = FUN, at the FP state fx1 refuse returned *)
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
  unfold pf_postm, PF_POSTr.
  eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
  replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
  destruct HNA2 as (HP2b & Hly2 & HS2).
  pose proof (a6_keeps_refuse B v pos lyc Sc Wc rg memc mdc PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse
    HB HJc2 HP2b) as HK.
  assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LINE).
  { apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc rg memc mdc PF_SC_LINE ly2 S2 W2 regs2
      mem2 md2 HB Hfx1 HJ2 Hly2 HS2 HP2b HK).
    intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
  apply (HFUN fx1 v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) f [AS (pf_tline (p_s v) o)]) nm o ln d).
  split; [exact HB2|]. split; [exact HMID|].
  split.
  - split; [exact HRC2|]. split.
    + destruct HK as (_ & _ & _ & K4). apply (a6_nm_move v pos (rdW Wc memc) _ nm HNM).
      intros a Ha. apply K4. left. exact Ha.
    + exact (a7_cnt_refuse_next cf (ln + 1) f [AS (pf_tline (p_s v) o)] (p_s v) o Ho HCNT).
  - apply (a5_rg_pres rg regs2 _ HP2).
    + apply Forall_app. split; [apply a5_RL_cs | apply a5_RM_cs].
    + exact HRG.
Qed.

(** ** The NOT-FOUND arm: a0 = 0 at strchr's return *)
Lemma w1_nc : forall n, HA_FUN B n ->
  forall v pos lyc Sc Wc (rX : bvmap 5 word) memc mdc cf cur nm o ln d lp,
  INV_HDR B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  getr rX 10 = w64 0 ->
  strchr (pf_tline (p_s v) o) RBR = None ->
  SRr SEGS Wc (cfg_at SEGS (BASE + W1_RET) rX memc mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
  intros n HFUN v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HINV R10 HSC.
  destruct HINV as (HB & HMID & HST & HSL & HLEN & HSTR & HINB & HHD & HRG).
  rewrite (a7_hdr_notclosed cf nm (ln + 1) (pf_tline (p_s v) o) HSC).
  pose proof HB as (_ & (HJ & _) & _).
  pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
  (* the seed, with a0 pinned to 0 *)
  pose proof (w1_seed0 Wc rX memc W1_RET 0) as HS0.
  assert (HS : st_ok_pi SEGS VAL (w1_E rX 0)
    (mkSS (ss_pc (w1_ss0 W1_RET)) (sr_set (ss_regs (w1_ss0 W1_RET)) (10%bv : bv 5) (SLit 0))
       (ss_mem (w1_ss0 W1_RET)) (ss_resv (w1_ss0 W1_RET)) (ss_facts (w1_ss0 W1_RET)))
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + W1_RET)) memc (seg_rom SEGS)))).
  { eapply (st_ok_pi_pin_reg' (w1_E rX 0) (w1_ss0 W1_RET) _ (10%bv : bv 5) 0 HS0);
      [cbn [ms_regs restrict mkst]; exact R10 | vm_compute; reflexivity]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts w1_ss0] in HS.
  assert (HEI : img_env VAL A_LIM (w1_E rX 0)) by apply w1_E_img.
  assert (SHOK : sh_ok SEGS a7_Bx [] (w1_E rX 0) (mrestrict (w_H Wc) memc)) by constructor.
  change (cfg_at SEGS (BASE + W1_RET) rX memc mdc)
    with (mkCfg (mkst rX (Z_to_bv 64 (BASE + W1_RET)) memc (seg_rom SEGS)) mdc).
  (* 0x87f78 .. 0x88060: the not-closed arm, a2 = F_notclosed's literal, then the call *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK Bspan.
  { w1_awr. }
  w1_same HF Hmem ms memc.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *.
  w1_ag HS rX [Z_to_bv 64 0] HAG.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [Z_to_bv 64 0] HS HAG
    ltac:(vm_compute; reflexivity)) as HPR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  assert (R24 : getr rX 24 = w64 (p_c v))
    by exact (a5_rg_get rX _ 24 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
  assert (R26 : getr rX 26 = w64 (ln + 1))
    by exact (a5_rg_get rX _ 26 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
  assert (R23 : getr rX 23 = w64 lp)
    by exact (a5_rg_get rX _ 23 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
  apply (w1_ref n HFUN v pos lyc Sc Wc (ms_regs ms) memc mdq cf cur nm o ln d lp F_notclosed).
  - exact (w1_base_regs fx v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ
      (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI)).
  - exact HMID.
  - exact HST.
  - exact HSTR.
  - exact HINB.
  - left. reflexivity.
  - apply (a5_rg_pres rX (ms_regs ms) _ HPR
      ltac:(apply Forall_app; split; [apply a5_RL_cs | apply a5_RM_cs])).
    eapply a5_rg_incl; [|exact HRG]. intros x Hx. apply in_app_or in Hx. apply in_or_app.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; apply in_or_app; left; exact Hx].
  - rewrite Q10, (w1_ew_reg rX 0 24 (24%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R24.
  - rewrite Q11, (w1_ew_reg rX 0 26 (26%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R26.
  - rewrite Q12. change 280%nat with (A_OBJ 39). exact (w1_lit_notclosed _ HEI).
  - rewrite Q13, (w1_ew_reg rX 0 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R23.
  - rewrite Q1. unfold A7_FUN, AF_reac_segconf_parse_file. reflexivity.
Qed.

(** ** The FOUND arm: a0 = lp + ci at strchr's return *)
Lemma w1_cl : forall n, HA_FUN B n -> HA_CLOSE B n ->
  forall v pos lyc Sc Wc (rX : bvmap 5 word) memc mdc cf cur nm o ln d lp ci,
  INV_HDR B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  getr rX 10 = w64 (lp + Z.of_nat ci) ->
  strchr (pf_tline (p_s v) o) RBR = Some ci ->
  SRr SEGS Wc (cfg_at SEGS (BASE + W1_RET) rX memc mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
  intros n HFUN HCLOSE v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci HINV R10 HSC.
  pose proof HINV as (HB & HMID & HST & HSL & HLEN & HSTR & HINB & HHD & HRG).
  pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HST7.
  pose proof HB as (_ & (HJ & _) & HOBJ & _).
  pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc HST7) as (HF1 & HF2 & HF3 & HF4).
  pose proof alloc_ceiling_lt as HACL.
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  (* where the ']' is, and the byte after it *)
  assert (HNUL : ~ In 0 (pf_tline (p_s v) o)) by (unfold pf_tline; apply w1_trim_nul).
  assert (Hci : (ci < length (pf_tline (p_s v) o))%nat).
  { rewrite (strchr_memchr _ RBR HNUL ltac:(lia)) in HSC. exact (memchr_lt _ _ _ HSC). }
  pose proof HINB as (HI1 & HI2).
  pose proof HSTR as ((HZS & _) & _).
  assert (HBYTE : rdW Wc memc (lp + Z.of_nat ci + 1) = Some (nth (S ci) (pf_tline (p_s v) o) 0)).
  { replace (lp + Z.of_nat ci + 1) with (lp + Z.of_nat (S ci)) by lia.
    rewrite (HZS (S ci) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite (w1_nth_app0 (pf_tline (p_s v) o) (S ci) ltac:(lia)). reflexivity. }
  set (bz := nth (S ci) (pf_tline (p_s v) o) 0) in HBYTE.
  assert (HBR : 0 <= bz < 256).
  { destruct (aview_byte SEGS (w_H Wc) memc _ _ HBYTE) as (_ & _ & _ & Hr). exact Hr. }
  assert (Hq1 : a7_buf v pos <= lp + Z.of_nat ci + 1) by (unfold a7_buf, PF_O_BUF in *; lia).
  assert (Hq2 : lp + Z.of_nat ci + 2 <= a7_buf v pos + 512) by (unfold a7_buf, PF_O_BUF in *; lia).
  assert (HRA : sa_addr (rdW Wc memc) (lp + Z.of_nat ci + 1) 1)
    by exact (a7_addr_buf B v pos lyc Sc Wc memc mdc _ 1 HST7 Hq1 ltac:(lia) ltac:(lia)).
  assert (R22 : getr rX 22 = w64 SHADOW_OFF)
    by exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn [a5_FI In]; tauto)).
  assert (Hqlo : 4096 <= lp + Z.of_nat ci) by (unfold a7_buf, PF_O_BUF in *; lia).
  assert (Hqhi : lp + Z.of_nat ci + 2 <= alloc_ceiling) by (unfold a7_buf, PF_O_BUF in *; lia).
  (* the seed of the found arm *)
  assert (U10 : bv_unsigned (ew (w1_E rX bz) 10) = lp + Z.of_nat ci).
  { rewrite (w1_ew_reg rX bz 10 (10%bv : bv 5) ltac:(vm_compute; reflexivity)), R10.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U22 : bv_unsigned (ew (w1_E rX bz) 22) = SHADOW_OFF).
  { rewrite (w1_ew_reg rX bz 22 (22%bv : bv 5) ltac:(vm_compute; reflexivity)), R22.
    unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
  assert (U32 : bv_unsigned (ew (w1_E rX bz) 32) = bz)
    by (rewrite w1_ew_bz; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL (w1_E rX bz) w1_ssF
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + W1_RET)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold w1_ssF. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold w1_rB, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (lp + Z.of_nat ci) 1 1%N (SOff 32 0) bz).
      + cbn [sv_denot]. rewrite w1_ew_bz, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + cbn. lia.
      + apply a7q_val_mem1; [exact HBYTE | exact HBR].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - split; [|split; exact I].
      cbn [w1_GF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10, U22, U32, !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
      repeat split; lia. }
  assert (HEI : img_env VAL A_LIM (w1_E rX bz)) by apply w1_E_img.
  assert (UBx : U (w1_E rX bz) a7_Bx = SHADOW_OFF)
    by (unfold a7_Bx; apply U_atom;
        [rewrite (w1_ew_reg rX bz 22 (22%bv : bv 5) ltac:(vm_compute; reflexivity)), R22; reflexivity
        | unfold SHADOW_OFF; lia]).
  assert (UE : U (w1_E rX bz) (SOff 10 0) = lp + Z.of_nat ci)
    by (apply U_atom;
        [rewrite (w1_ew_reg rX bz 10 (10%bv : bv 5) ltac:(vm_compute; reflexivity)), R10; reflexivity | lia]).
  assert (SHOK : sh_ok SEGS a7_Bx w1_SHF (w1_E rX bz) (mrestrict (w_H Wc) memc)).
  { unfold sh_ok, w1_SHF. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H Wc) memc (w1_E rX bz) a7_Bx 10%nat (lp + Z.of_nat ci + 1) 1
      (lp + Z.of_nat ci) 1 2 (proj1 (proj2 (proj2 (proj2 HRA)))) UBx UE); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF3. unfold SHADOW_OFF.
    unfold a7_buf, PF_O_BUF in Hq1, Hq2. lia. }
  change (cfg_at SEGS (BASE + W1_RET) rX memc mdc)
    with (mkCfg (mkst rX (Z_to_bv 64 (BASE + W1_RET)) memc (seg_rom SEGS)) mdc).
  (* 0x87f78 .. 0x87f94: inline check 8 and the byte after the ']' *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK Bspan.
  { w1_awr. }
  w1_same HF Hmem1 ms memc.
  rename ms into ms1. rename HF into HFr1.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK Bspan.
  - (* the byte is the line's NUL: CLOSE *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
        assert (E32 : ew Ex 32 = Z_to_bv 64 bz)
          by (first [exact (w1_ew_bz rX bz) | rewrite ?ew_ewset_other by lia; exact (w1_ew_bz rX bz)])
    end.
    pose proof (w1_br_eq0 _ 32 bz true E32 ltac:(lia) Hc) as Hbz.
    apply Z.eqb_eq in Hbz. clear Hc.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK Bspan A7_CLOSE.
    { w1_awr. }
    w1_same HF Hmem2 ms (ms_mem ms1).
    (* the second run's goal collapses the two vm-backing layers; the journal keeps both *)
    rewrite ?YA0o.wvb_collapse in HJ.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
    pmkst HS. rewrite Hmem2, Hmem1 in HJ |- *.
    w1_ag HS rX [Z_to_bv 64 bz] HAG.
    pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [Z_to_bv 64 bz] HS HAG
      ltac:(vm_compute; reflexivity)) as HPR.
    prreg HS (10%bv : bv 5) Q10.
    assert (C10 : getr (ms_regs ms) 10 = w64 (lp + Z.of_nat ci)).
    { rewrite Q10. rewrite ?ew_ewset_other by lia.
      rewrite (w1_ew_reg rX bz 10 (10%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R10. }
    apply (HCLOSE fx v pos lyc Sc Wc (ms_regs ms) memc mdq cf cur nm o ln d lp ci).
    unfold INV_CLOSE.
    split.
    { exact (w1_base_regs fx v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ
        (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI)). }
    split; [exact HMID|]. split; [exact HST|]. split; [exact HSL|].
    split; [exact HLEN|]. split; [exact HSTR|]. split; [exact HINB|]. split; [exact HHD|].
    split; [exact HSC|]. split; [exact Hbz|].
    pose proof (proj1 (a5_rg_app rX (PF_RL v pos) _) HRG) as (HRG1 & HRG23).
    pose proof (proj1 (a5_rg_app rX (PF_RM v o ln) _) HRG23) as (HRG2 & HR3).
    unfold pf_rg. apply Forall_app. split.
    { apply (a5_rg_pres rX (ms_regs ms) _ HPR (a5_RL_cs v pos) HRG1). }
    apply Forall_app. split.
    { apply (a5_rg_pres rX (ms_regs ms) _ HPR (a5_RM_cs v o ln) HRG2). }
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (HPR 20 ltac:(unfold acallee_saved; lia)).
      exact (a5_rg_get rX _ 20 _ HR3 ltac:(cbn [In]; tauto)).
    + rewrite (HPR 25 ltac:(unfold acallee_saved; lia)).
      exact (a5_rg_get rX _ 25 _ HR3 ltac:(cbn [In]; tauto)).
    + rewrite (HPR 23 ltac:(unfold acallee_saved; lia)).
      exact (a5_rg_get rX _ 23 _ HR3 ltac:(cbn [In]; tauto)).
    + exact C10.
  - (* a byte follows the ']': the F_after refusal *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
        assert (E32 : ew Ex 32 = Z_to_bv 64 bz)
          by (first [exact (w1_ew_bz rX bz) | rewrite ?ew_ewset_other by lia; exact (w1_ew_bz rX bz)])
    end.
    pose proof (w1_br_eq0 _ 32 bz false E32 ltac:(lia) Hc) as Hbz.
    apply Z.eqb_neq in Hbz. clear Hc.
    rewrite (a7_hdr_after cf nm (ln + 1) (pf_tline (p_s v) o) ci HSC Hbz).
    paj_run_tok (paj_run B LAWS) HS HJ SHOK Bspan.
    { w1_awr. }
    w1_same HF Hmem3 ms (ms_mem ms1).
    rewrite ?YA0o.wvb_collapse in HJ.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
    pmkst HS. rewrite Hmem3, Hmem1 in HJ |- *.
    w1_ag HS rX [Z_to_bv 64 bz] HAG.
    pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [Z_to_bv 64 bz] HS HAG
      ltac:(vm_compute; reflexivity)) as HPR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    assert (R24 : getr rX 24 = w64 (p_c v))
      by exact (a5_rg_get rX _ 24 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
    assert (R26 : getr rX 26 = w64 (ln + 1))
      by exact (a5_rg_get rX _ 26 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
    assert (R23 : getr rX 23 = w64 lp)
      by exact (a5_rg_get rX _ 23 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
    apply (w1_ref n HFUN v pos lyc Sc Wc (ms_regs ms) memc mdq cf cur nm o ln d lp F_after).
    + exact (w1_base_regs fx v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ
        (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI)).
    + exact HMID.
    + exact HST.
    + exact HSTR.
    + exact HINB.
    + right. reflexivity.
    + apply (a5_rg_pres rX (ms_regs ms) _ HPR
        ltac:(apply Forall_app; split; [apply a5_RL_cs | apply a5_RM_cs])).
      eapply a5_rg_incl; [|exact HRG]. intros x Hx. apply in_app_or in Hx. apply in_or_app.
      destruct Hx as [Hx|Hx]; [left; exact Hx | right; apply in_or_app; left; exact Hx].
    + rewrite Q10. rewrite ?ew_ewset_other by lia.
      rewrite (w1_ew_reg rX bz 24 (24%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R24.
    + rewrite Q11. rewrite ?ew_ewset_other by lia.
      rewrite (w1_ew_reg rX bz 26 (26%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R26.
    + rewrite Q12. rewrite ?ew_ewset_other by lia. change 279%nat with (A_OBJ 38).
      exact (w1_lit_after _ HEI).
    + rewrite Q13. rewrite ?ew_ewset_other by lia.
      rewrite (w1_ew_reg rX bz 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)). exact R23.
    + rewrite Q1. unfold A7_FUN, AF_reac_segconf_parse_file. reflexivity.
Qed.

(** ** HDR: the strchr call, then one of the two arms *)
Lemma w1_hdr : forall n, HA_FUN B n -> HA_CLOSE B n -> H_HDR B n.
Proof.
  intros n HFUN HCLOSE. unfold H_HDR.
  intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HINV.
  pose proof HINV as (HB & HMID & HST & HSL & HLEN & HSTR & HINB & HHD & HRG).
  pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HST7.
  pose proof HB as (_ & (HJ & _) & HOBJ & _).
  pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
  pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  destruct (a7_stk B v pos lyc Sc Wc memc mdc HST7) as (Hsp16 & Hceil & Hslo & Hs132 & Hs1rng & Ho16).
  pose proof STK_values as (_ & _ & _ & SPF & _).
  pose proof alloc_ceiling_lt as HACL. pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  assert (Hes : ESTACK = 4096) by reflexivity.
  (* the run HDR -> the strchr call *)
  pose proof (w1_seed0 Wc rX memc PF_HDR 0) as HS.
  assert (HEI : img_env VAL A_LIM (w1_E rX 0)) by apply w1_E_img.
  assert (SHOK : sh_ok SEGS a7_Bx [] (w1_E rX 0) (mrestrict (w_H Wc) memc)) by constructor.
  change (cfg_at SEGS (BASE + PF_HDR) rX memc mdc)
    with (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_HDR)) memc (seg_rom SEGS)) mdc).
  paj_run_tok (paj_run B LAWS) HS HJ SHOK Bspan.
  { w1_awr. }
  w1_same HF Hmem ms memc.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *.
  w1_ag HS rX [Z_to_bv 64 0] HAG.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [Z_to_bv 64 0] HS HAG
    ltac:(vm_compute; reflexivity)) as HPR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  assert (R23 : getr rX 23 = w64 lp)
    by exact (a5_rg_get rX _ 23 _ HRG ltac:(cbn [PF_RL PF_RM app In]; tauto)).
  assert (HFI2 : pf_rg (ms_regs ms) (a5_FI B v))
    by exact (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI).
  assert (HB' : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE)
    by exact (w1_base_regs fx v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ HFI2).
  pose proof (a7_st_of_base B v pos lyc Sc Wc (ms_regs ms) memc mdq HB') as HST7'.
  destruct (a5_geo B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE HB')
    as (HARx & Hlyx & Hfinx & Gx & _).
  assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v))
    by exact (a5_rg_get _ _ 2 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
  assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B))
    by exact (a5_rg_get _ _ 3 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
  assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B))
    by exact (a5_rg_get _ _ 4 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
  assert (Csp : spZ (ms_regs ms) = pf_s1 v)
    by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + W1_RET))
    by (rewrite Q1; unfold W1_RET, AF_reac_segconf_parse_file; reflexivity).
  assert (Hra' : YK0s.ret_ok (getr (ms_regs ms) 1))
    by (rewrite C1; apply ret_ok_codeptr_v;
        [unfold W1_RET, AF_reac_segconf_parse_file; lia | reflexivity]).
  assert (C10 : getr (ms_regs ms) 10 = w64 lp) by (rewrite Q10; exact R23).
  assert (C11 : getr (ms_regs ms) 11 = w64 0x5d) by (rewrite Q11; reflexivity).
  destruct (a7_strchr_pre_87f74 B v pos lyc Sc Wc memc mdq (ms_regs ms) lp (pf_tline (p_s v) o)
    HST7' Csp Hra' C3 C4 C10 C11 HSTR HINB)
    as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  (* the call *)
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
      (SIG SS___interceptor_trampoline_strchr) Wc (ms_regs ms) memc STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
      (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + W1_RET)) _ HJ).
    - rewrite Csp. lia.
    - exact Ho16.
    - lia.
    - unfold ESTACK; lia.
    - rewrite SPF. unfold ESTACK. lia.
    - exact C1.
    - intros a HFalse. destruct HFalse.
    - apply (ASTRCHR fx lyc Sc Wc (ms_regs ms) memc mdq lp 0x5d (seg_spec.zb (pf_tline (p_s v) o)));
        [exact P1 | exact P2 | exact P3 | exact P4 | exact P5 | exact P6 | exact P7 | exact P8 | exact P9
        | exact P10]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
  (* the cut's facts at the call's new memory: the entry kept every byte outside its own window *)
  assert (KW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a ->
    rdW Wc mem2 a = rdW Wc memc a).
  { intros sl shw a Ha Hn. apply (HK2 a Ha); [|intros HFalse; destruct HFalse].
    intros Hw. apply Hn. unfold a5_Wrx. left. rewrite SPF. unfold ESTACK in *. lia. }
  pose proof (KW true true) as KL.
  assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
  { intros a Hv. rewrite (w1_view_wrap SEGS (w_H Wc) mem2 a).
    rewrite (w1_view_wrap SEGS (w_H Wc) memc a) in Hv.
    assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_sp0 v - STK_reac_segconf_parse_file)) as [Hb1|Hb1];
      [|destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_sp0 v)) as [Hb2|Hb2]].
    - rewrite (HK2 (a mod 2 ^ 64) Ha ltac:(rewrite SPF in Hb1; unfold ESTACK in *; lia)
        ltac:(intros HFalse; destruct HFalse)). exact Hv.
    - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply (aview_some_of_apresent SEGS). apply Hpres2. lia.
    - rewrite (HK2 (a mod 2 ^ 64) Ha ltac:(unfold ESTACK in *; lia)
        ltac:(intros HFalse; destruct HFalse)). exact Hv. }
  assert (HFI3 : pf_rg regs2 (a5_FI B v)) by exact (a5_rg_pres _ _ _ HP2 (a5_FI_cs B v) HFI2).
  assert (HFSH2 : pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_LINE).
  { apply (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc mem2) true PF_SC_LINE G (KW true false)).
    exact (proj2 (proj2 (proj2 (proj2 HB')))). }
  assert (HB2 : pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE).
  { apply (a5_move0 B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE
      HB' HJ2).
    - exists (st_fs Sc). destruct Sc; reflexivity.
    - apply Permutation_refl.
    - exact KL.
    - exact KV.
    - exact HFI3.
    - exact HFSH2. }
  (* the line, the record and the slot at the new memory *)
  (* buf is inside A5's write set but far below the call's own window, so KL does not give this one *)
  assert (KLOW : forall a, 0 <= a < alloc_ceiling -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha. apply (HK2 a ltac:(lia)); [|intros HFalse; destruct HFalse].
    intros Hw. rewrite SPF in G1. unfold ESTACK in *. lia. }
  assert (HSTR2 : sa_str (rdW Wc mem2) lp (pf_tline (p_s v) o)).
  { destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc HST7) as (HFa & HFb & _).
    pose proof HINB as (HI1 & HI2). unfold PF_O_BUF in HI1, HI2.
    apply (reac_segconf_parse.sa_str_low (rdW Wc memc) (rdW Wc mem2) lp (pf_tline (p_s v) o) HSTR);
      [lia | lia | exact KLOW]. }
  assert (HST2 : pf_st v pos (rdW Wc mem2) cf cur nm (length (skipn o (p_s v)))).
  { destruct HOBJ as (_ & _ & _ & _ & HHC & _).
    apply (a5_keep_st B v pos lyc Sc Wc memc mdq Wc mem2);
      solve [exact Gx | exact HARx | exact Hfinx | exact Hlyx | exact KL | exact KV | exact HHC
            | exact HST]. }
  assert (HSL2 : pf_sl (rdW Wc mem2) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)]).
  { apply (a5_keep_slot v pos (rdW Wc memc) (rdW Wc mem2) true (pf_cur_ptr (p_c v) cur) G
      (KW false true)).
    exact HSL. }
  assert (HINV2 : INV_HDR B n v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d lp).
  { split; [exact HB2|]. split; [exact HMID|]. split; [exact HST2|]. split; [exact HSL2|].
    split; [exact HLEN|]. split; [exact HSTR2|]. split; [exact HINB|]. split; [exact HHD|].
    apply (a5_rg_pres (ms_regs ms) regs2 _ HP2).
    - apply Forall_app; split; [apply a5_RL_cs|]. apply Forall_app; split; [apply a5_RM_cs|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
    - apply (a5_rg_pres rX (ms_regs ms) _ HPR); [|exact HRG].
      apply Forall_app; split; [apply a5_RL_cs|]. apply Forall_app; split; [apply a5_RM_cs|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
  (* strchr's answer *)
  assert (HZS : seg_spec.zs (seg_spec.zb (pf_tline (p_s v) o)) = pf_tline (p_s v) o).
  { destruct (a7_astr_of_sa Wc memc lp (pf_tline (p_s v) o) HSTR) as (_ & _ & _ & HE & _). exact HE. }
  assert (HNUL : ~ In 0 (pf_tline (p_s v) o)) by (unfold pf_tline; apply w1_trim_nul).
  destruct HQ as [(HA0 & HNIN) | (j & HFST & HA0)].
  - (* not found *)
    apply (w1_nc n HFUN v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d lp HINV2 HA0).
    rewrite <- HZS. apply w1_strchr_none; [rewrite HZS; exact HNUL | lia | exact HNIN].
  - (* found at j *)
    apply (w1_cl n HFUN HCLOSE v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d lp j HINV2 HA0).
    rewrite <- HZS. apply w1_strchr_first; [rewrite HZS; exact HNUL | lia | exact HFST].
Qed.

End x.

(** ** The piece, as pf_a7_m.v states it *)
Theorem a7_w1 : A7_S_HDR B.
Proof. intros f0 n HFUN HCLOSE. exact (w1_hdr (fx := f0) n HFUN HCLOSE). Qed.

End e.
End f.
End d.
