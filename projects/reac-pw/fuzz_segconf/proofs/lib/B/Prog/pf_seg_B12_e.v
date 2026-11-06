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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 343 of its 384 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B12 of
   reac_segconf_parse_file's walk, the entry arm (reac_segconf.c:88-93 inside parse_bool, R:273-276): the cut IGN
   0x887e0 (H_IGN of lib/B/Prog/pf_pieces.v) and the internal cuts R1 0x887f4, R2 0x8880c of
   lib/B/Prog/pf_seg_B12_k.v. The B12 segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of
   reac_segconf_parse_file's walk, segment B12).
   ADAPTED from a working branch (the spine and the six tests, pf_a12_pure.v) and the unit owner's UBSan piece
   walk lib/U/Prog/pf_p8.v, re-derived on image B's code
   (the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     IGN 0x887e0  a1 = "yes" (listing object 50), s7 = val (slot 0x70), a0 = s7, strcasecmp (0x887f0) -> R1
     R1  0x887f4  `li s3,1`, `beqz a0` -> 0x88df4 `ld a3,192(s1)` -> STORE (b = true); a1 = "true" (object 51),
                  a0 = s7, strcasecmp (0x88808) -> R2
     R2  0x8880c  `beqz a0` -> 0x88df4 -> STORE (b = true); check B#22 (0x88810-0x88824: load1 at val; slow arm
                  0x89070-0x89078, error call 0x892bc errpath_load1): the obligation that val is addressable (val[0]
                  or its NUL, in buf: b12_buf_shadow); a3 = cur (slot 0xc0), a4 = val, s7 = val[0], `bne s7,'1'` ->
                  NO 0x88850; check B#23 (0x88834-0x88844: load1 at val + 1; slow arm 0x890b4-0x890bc, error call
                  0x892d8): val + 1 is val[1] or the NUL since val[0] = '1'; `lbu a0,0(a0)`, `beqz a0` -> 0x88df8
                  STORE (b = true) else NO.
   No UBSan trap site lies in this file; the inline checks are B#22 and B#23. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pf_p8_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B12_k pf_seg_B12_n.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module P8 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.pf_p8_lemmas.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run that writes nothing: the environment agrees with E0 below 48 (HAE), the memory is memc1 (KM) *)
Ltac b12e_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    clear HFr HG HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.
(* the same after a run that stops at a call (the state is st_ok at the callee) *)
Ltac b12e_afterc E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    clear HFr HG HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.
Ltac b12e_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.


(** ** R2 0x8880c: after strcasecmp(val, "true"); s7 is re-seeded as val's atom 32 so the byte loads find val's
    region *)
Lemma b12_r2_ok : B12_STORE_stmt B -> B12_NO_stmt B -> B12_R2_stmt B.
Proof.
intros HSTORE HNO. unfold B12_R2_stmt.
intros e regs1 memc1 mdc1 HE HM N1 HA0 R19 R23.
destruct (b12_b1 B e regs1 memc1 mdc1 HE HM) as (b1 & Hb1 & Hb1r).
destruct (b12_valbytes B e regs1 memc1 mdc1 HE HM) as (VB & NZ & BV & VT).
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (_ & _ & _ & HF1 & HF2 & _ & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _ & _ & Hv1 & Hv2 & _).
unfold PF_O_BUF in Hv1, Hv2. pose proof alloc_ceiling_value as (Hac & _).
pose proof (b12_seed B e regs1 memc1 mdc1 B12_R2 b1 HE HM Hb1 Hb1r) as HS0.
assert (HEI : img_env VAL A_LIM (b12_E regs1 e b1)) by (unfold b12_E; apply Eimg_env).
assert (HA0' : env_agree 32 (Ereg regs1 (b12_xs e b1)) (b12_E regs1 e b1))
  by (split; [intros n0 Hn0; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (b12_E regs1 e b1) n = getr regs1 r)
  by (intros n r Hn; unfold b12_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew (b12_E regs1 e b1) (32 + j) = nth j (b12_xs e b1) (Z_to_bv 64 0))
  by (intros j Hj; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth b12_xs] in E32, E34, E37, E38. clear EX.
assert (E10 : ew (b12_E regs1 e b1) 10 = getr regs1 10) by (apply EE; reflexivity).
assert (E19 : ew (b12_E regs1 e b1) 19 = getr regs1 19) by (apply EE; reflexivity).
assert (E20 : ew (b12_E regs1 e b1) 20 = w64 SHADOW_OFF).
{ rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl).
  apply (b12_kreg B e regs1 memc1 mdc1 20 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto. }
(* s7 = val: the seed's register 23 is val's atom 32 *)
pose proof (ast_ok_pi_set_reg_fp (b12_E regs1 e b1) (b12_ss B12_R2)
  (restrict (w_H (e_W e)) (mkst regs1 (Z_to_bv 64 (BASE + B12_R2)) memc1 (seg_rom SEGS))) (23%bv) (SOff 32 0) HS0
  eq_refl ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R23; reflexivity))
  as HS.
clear HS0.
revert HS HEI HA0' EE E10 E19 E20 E32 E34 E37 E38. generalize (b12_E regs1 e b1) as E0.
intros E0 HS HEI HA0' EE E10 E19 E20 E32 E34 E37 E38.
pose proof (env_agree_refl 48 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) memc1 a = rdW (e_W e) memc1 a) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS b12_Bx [] E0 (mrestrict (w_H (e_W e)) memc1)) by constructor.
pose proof HM as (HJ & _ & _).
pose proof (bv_unsigned_in_range 64 (getr regs1 10)) as R10r. unfold bv_modulus in R10r. cbn in R10r.
assert (V0 : 0 <= nth 0 (e_val e) 0 < 256) by (apply P8.p8_nth_val; intros x Hx; pose proof (BV x Hx); lia).
unfold b12_at.
(* 0x8880c beqz a0 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* strcasecmp(val, "true") = 0: b = true *)
  pose proof (b12_br_eq _ 10 (getr regs1 10) 0 true (b12_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) ltac:(lia) Hc) as Z0.
  apply b12_w0 in Z0. apply HA0 in Z0. clear Hc.
  pose proof (P8.p8_pb_true (e_val e) Z0) as PB.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B12_STORE. { b12e_awr. }
  b12e_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (19%bv : bv 5) N19. prreg HS (13%bv : bv 5) N13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (HSTORE e true rg mm mdn HE) end.
  + exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
  + exact PB.
  + rewrite N19. exact (b12_ag_ew _ _ _ 19 _ HAE ltac:(lia) (eq_trans E19 R19)).
  + rewrite N13. exact (b12_ag_ew _ _ _ 34 _ HAE ltac:(lia) E34).
- (* strcasecmp(val, "true") <> 0 *)
  pose proof (b12_br_eq _ 10 (getr regs1 10) 0 false (b12_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) ltac:(lia) Hc) as Z0.
  apply b12_wn0 in Z0. assert (N2 : SegModel.strcasecmp (e_val e) S_true <> 0) by (intros H; apply Z0, HA0, H).
  clear Hc Z0.
  (* 0x88810 .. 0x88830: check B#22, a3 = cur, a4 = val, s7 = val[0], li a0,49, bne *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold b12_Bx. rewrite (U_atom _ 20 SHADOW_OFF (b12_ag_ew _ _ _ 20 _ HAE ltac:(lia) E20)) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom _ 32 (e_vp e) (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) by lia.
    lazymatch goal with |- context [YCbn.rd_of SEGS (mrestrict (w_H (e_W e)) ?m)] =>
      change (YCbn.rd_of SEGS (mrestrict (w_H (e_W e)) m)) with (rdW (e_W e) m) end.
    apply (b12_ra_ext (rdW (e_W e) memc1)); [exact KM | lia | lia |].
    exact (proj1 (b12_buf_shadow B e regs1 memc1 mdc1 (e_vp e) 1 HE HM ltac:(unfold PF_O_BUF; lia)
      ltac:(unfold PF_O_BUF; lia) ltac:(lia))). }
  { b12e_awr. }
  b12e_after E0 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* val[0] <> '1': NO *)
    pose proof (b12_br_ne _ 37 (w64 (nth 0 (e_val e) 0)) 49 true (b12_ag_ew _ _ _ 37 _ HAE ltac:(lia) E37)
      ltac:(lia) Hc) as C0.
    unfold w64 in C0. rewrite unsigned_lit_small in C0 by lia.
    apply negb_true_iff, Z.eqb_neq in C0. clear Hc.
    assert (N3 : strcmp (e_val e) [49] <> 0).
    { intros H. apply (proj1 (P8.p8_strcmp1 (e_val e) 49 NZ ltac:(lia))) in H. rewrite H in C0. apply C0. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B12_NO. { b12e_awr. }
    b12e_after E0 HAE KM.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
      ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
    prreg HS (14%bv : bv 5) N14. prreg HS (23%bv : bv 5) N23.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (HNO e rg mm mdn HE) end.
    * exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
    * exact N1.
    * exact N2.
    * exact N3.
    * rewrite N14. exact (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32).
    * rewrite N23. exact (b12_ag_ew _ _ _ 37 _ HAE ltac:(lia) E37).
  + (* val[0] = '1': check B#23, val[1] *)
    pose proof (b12_br_ne _ 37 (w64 (nth 0 (e_val e) 0)) 49 false (b12_ag_ew _ _ _ 37 _ HAE ltac:(lia) E37)
      ltac:(lia) Hc) as C0.
    unfold w64 in C0. rewrite unsigned_lit_small in C0 by lia.
    apply negb_false_iff, Z.eqb_eq in C0. clear Hc.
    pose proof (P8.p8_len1 (e_val e) 49 ltac:(lia) C0) as L1.
    assert (B1 : b1 = nth 1 (e_val e) 0).
    { pose proof (VB 1%nat L1) as V1. replace (e_vp e + Z.of_nat 1) with (e_vp e + 1) in V1 by lia.
      rewrite Hb1 in V1. injection V1 as V1. exact V1. }
    paj_run_tok RUN HS HJ SHOK Bspan.
    { unfold b12_Bx. rewrite (U_atom _ 20 SHADOW_OFF (b12_ag_ew _ _ _ 20 _ HAE ltac:(lia) E20)) by (unfold SHADOW_OFF; lia).
      rewrite (U_atom_off _ 32 (e_vp e) 1 (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) by lia.
      lazymatch goal with |- context [YCbn.rd_of SEGS (mrestrict (w_H (e_W e)) ?m)] =>
        change (YCbn.rd_of SEGS (mrestrict (w_H (e_W e)) m)) with (rdW (e_W e) m) end.
      apply (b12_ra_ext (rdW (e_W e) memc1)); [exact KM | lia | lia |].
      exact (proj1 (b12_buf_shadow B e regs1 memc1 mdc1 (e_vp e + 1) 1 HE HM ltac:(unfold PF_O_BUF; lia)
        ltac:(unfold PF_O_BUF; lia) ltac:(lia))). }
    { b12e_awr. }
    b12e_after E0 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* val[1] = 0: val = "1", b = true *)
      pose proof (b12_br_eq _ 38 (w64 b1) 0 true (b12_ag_ew _ _ _ 38 _ HAE ltac:(lia) E38) ltac:(lia) Hc) as Z1.
      unfold w64 in Z1. rewrite unsigned_lit_small in Z1 by lia. apply Z.eqb_eq in Z1. clear Hc.
      assert (S1 : strcmp (e_val e) [49] = 0).
      { apply (P8.p8_strcmp1 (e_val e) 49 NZ ltac:(lia)).
        apply (P8.p8_one_byte (e_val e) 49 NZ ltac:(lia) C0). rewrite <- B1. exact Z1. }
      pose proof (P8.p8_pb_one (e_val e) S1) as PB.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B12_STORE. { b12e_awr. }
      b12e_after E0 HAE KM.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
        ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      prreg HS (19%bv : bv 5) N19. prreg HS (13%bv : bv 5) N13.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
        apply (HSTORE e true rg mm mdn HE) end.
      -- exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
      -- exact PB.
      -- rewrite N19. exact (b12_ag_ew _ _ _ 19 _ HAE ltac:(lia) (eq_trans E19 R19)).
      -- rewrite N13. exact (b12_ag_ew _ _ _ 34 _ HAE ltac:(lia) E34).
    * (* val[1] <> 0: NO *)
      pose proof (b12_br_eq _ 38 (w64 b1) 0 false (b12_ag_ew _ _ _ 38 _ HAE ltac:(lia) E38) ltac:(lia) Hc) as Z1.
      unfold w64 in Z1. rewrite unsigned_lit_small in Z1 by lia. apply Z.eqb_neq in Z1. clear Hc.
      assert (N3 : strcmp (e_val e) [49] <> 0).
      { intros H. apply (proj1 (P8.p8_strcmp1 (e_val e) 49 NZ ltac:(lia))) in H.
        apply Z1. rewrite B1. apply (proj1 (P8.p8_one_byte (e_val e) 49 NZ ltac:(lia) C0)). exact H. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B12_NO. { b12e_awr. }
      b12e_after E0 HAE KM.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
        ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      prreg HS (14%bv : bv 5) N14. prreg HS (23%bv : bv 5) N23.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
        apply (HNO e rg mm mdn HE) end.
      -- exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
      -- exact N1.
      -- exact N2.
      -- exact N3.
      -- rewrite N14. exact (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32).
      -- rewrite N23. rewrite C0. exact (b12_ag_ew _ _ _ 37 _ HAE ltac:(lia) (eq_trans E37 (f_equal w64 C0))).
Qed.

(** ** R1 0x887f4 and IGN 0x887e0: the "yes" and "true" calls *)
Section c.
Hypothesis TL : PALib B.
Hypothesis ASCMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis OBJ : seg_val_objs (PI := PI).

Lemma b12_r1_ok : B12_STORE_stmt B -> B12_R2_stmt B -> B12_R1_stmt B.
Proof.
intros HSTORE HR2. unfold B12_R1_stmt.
intros e regs1 memc1 mdc1 HE HM HA0 R23.
destruct (b12_b1 B e regs1 memc1 mdc1 HE HM) as (b1 & Hb1 & Hb1r).
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (_ & _ & _ & HF1 & HF2 & _ & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _ & _ & Hv1 & Hv2 & _).
unfold PF_O_BUF in Hv1, Hv2. pose proof alloc_ceiling_value as (Hac & _).
pose proof (b12_seed B e regs1 memc1 mdc1 B12_R1 b1 HE HM Hb1 Hb1r) as HS.
assert (HEI : img_env VAL A_LIM (b12_E regs1 e b1)) by (unfold b12_E; apply Eimg_env).
assert (HA0' : env_agree 32 (Ereg regs1 (b12_xs e b1)) (b12_E regs1 e b1))
  by (split; [intros n0 Hn0; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (b12_E regs1 e b1) n = getr regs1 r)
  by (intros n r Hn; unfold b12_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew (b12_E regs1 e b1) (32 + j) = nth j (b12_xs e b1) (Z_to_bv 64 0))
  by (intros j Hj; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 2%nat ltac:(lia)) as E34. cbn [Nat.add nth b12_xs] in E34. clear EX.
assert (E10 : ew (b12_E regs1 e b1) 10 = getr regs1 10) by (apply EE; reflexivity).
assert (E23 : ew (b12_E regs1 e b1) 23 = getr regs1 23) by (apply EE; reflexivity).
revert HS HEI HA0' EE E10 E23 E34. generalize (b12_E regs1 e b1) as E0.
intros E0 HS HEI HA0' EE E10 E23 E34.
pose proof (env_agree_refl 48 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) memc1 a = rdW (e_W e) memc1 a) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS b12_Bx [] E0 (mrestrict (w_H (e_W e)) memc1)) by constructor.
pose proof HM as (HJ & _ & _).
pose proof (bv_unsigned_in_range 64 (getr regs1 10)) as R10r. unfold bv_modulus in R10r. cbn in R10r.
unfold b12_at.
(* 0x887f4 li s3,1; 0x887f8 beqz a0 *)
paj_run_tok RUN HS HJ SHOK Bspan. { b12e_awr. }
b12e_after E0 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* strcasecmp(val, "yes") = 0: b = true *)
  pose proof (b12_br_eq _ 10 (getr regs1 10) 0 true (b12_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) ltac:(lia) Hc) as Z0.
  apply b12_w0 in Z0. apply HA0 in Z0. clear Hc.
  pose proof (P8.p8_pb_yes (e_val e) Z0) as PB.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B12_STORE. { b12e_awr. }
  b12e_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (19%bv : bv 5) N19. prreg HS (13%bv : bv 5) N13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (HSTORE e true rg mm mdn HE) end.
  + exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
  + exact PB.
  + rewrite N19. reflexivity.
  + rewrite N13. exact (b12_ag_ew _ _ _ 34 _ HAE ltac:(lia) E34).
- (* strcasecmp(val, "yes") <> 0: strcasecmp(val, "true") *)
  pose proof (b12_br_eq _ 10 (getr regs1 10) 0 false (b12_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) ltac:(lia) Hc) as Z0.
  apply b12_wn0 in Z0. assert (N1 : SegModel.strcasecmp (e_val e) S_yes <> 0) by (intros H; apply Z0, HA0, H).
  clear Hc Z0.
  paj_run_tok RUN HS HJ SHOK Bspan. { b12e_awr. }
  b12e_afterc E0 HAE KM.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
  prreg HS (Z_to_bv 5 19) Q19. prreg HS (Z_to_bv 5 23) Q23.
  pmkst HS.
  apply (b12_call B TL ASCMP e _ _ _ S_true B12_R2 _ HE).
  + exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
  + unfold B12_LITS. cbn [In]. tauto.
  + rewrite Q10. exact (b12_ag_ew _ _ _ 23 _ HAE ltac:(lia) (eq_trans E23 R23)).
  + rewrite Q11. pose proof b12_lits as (_ & L2 & _ & _ & _ & _ & _ & L51 & _ & _ & _ & _ & _).
    rewrite L2, <- L51. apply (b12_obj OBJ _ 51 HEI); vm_compute; lia.
  + exact Q1.
  + unfold B12_R2, AF_reac_segconf_parse_file. lia.
  + reflexivity.
  + intros regs2 mem2 md2 HM2 HP2 HQ2.
    apply (HR2 e regs2 mem2 md2 HE HM2 N1 HQ2).
    * apply (b12_bvr _ _ 19); [reflexivity|]. rewrite (HP2 19 ltac:(unfold acallee_saved; lia)).
      rewrite Q19. reflexivity.
    * apply (b12_bvr _ _ 23); [reflexivity|]. rewrite (HP2 23 ltac:(unfold acallee_saved; lia)).
      rewrite Q23. exact (b12_ag_ew _ _ _ 23 _ HAE ltac:(lia) (eq_trans E23 R23)).
Qed.

(* IGN 0x887e0: H_IGN, from the cut's state *)
Lemma b12_ign_ok : B12_R1_stmt B -> forall n, HA_KREF B n -> HA_PROV2 B n -> H_IGN B n.
Proof.
intros HR1 n HK HP v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HI K1 K2 K3.
pose (e := mkB12 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val).
assert (HE : b12_ent B e).
{ split; [exact HI|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact HK | exact HP]. }
assert (HM : b12_mid B e rX memc mdc).
{ pose proof HI as ((_ & HFI & _) & _). destruct HFI as (HJ0 & _).
  split; [exact HJ0|]. split; [intros a _ _; reflexivity | intros r _; reflexivity]. }
change (SRr SEGS (e_W e) (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_IGN)) memc (seg_rom SEGS)) mdc) (b12_post B e)).
clearbody e. clear HI K1 K2 K3 HK HP.
rename rX into regs1. rename memc into memc1. rename mdc into mdc1.
destruct (b12_b1 B e regs1 memc1 mdc1 HE HM) as (b1 & Hb1 & Hb1r).
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (_ & _ & _ & HF1 & HF2 & _ & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _ & _ & Hv1 & Hv2 & _).
unfold PF_O_BUF in Hv1, Hv2. pose proof alloc_ceiling_value as (Hac & _).
pose proof (b12_seed B e regs1 memc1 mdc1 PF_IGN b1 HE HM Hb1 Hb1r) as HS.
assert (HEI : img_env VAL A_LIM (b12_E regs1 e b1)) by (unfold b12_E; apply Eimg_env).
assert (HA0' : env_agree 32 (Ereg regs1 (b12_xs e b1)) (b12_E regs1 e b1))
  by (split; [intros n0 Hn0; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EX : forall j, (j < 7)%nat -> ew (b12_E regs1 e b1) (32 + j) = nth j (b12_xs e b1) (Z_to_bv 64 0))
  by (intros j Hj; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. cbn [Nat.add nth b12_xs] in E32. clear EX.
revert HS HEI HA0' E32. generalize (b12_E regs1 e b1) as E0.
intros E0 HS HEI HA0' E32.
pose proof (env_agree_refl 48 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) memc1 a = rdW (e_W e) memc1 a) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS b12_Bx [] E0 (mrestrict (w_H (e_W e)) memc1)) by constructor.
pose proof HM as (HJ & _ & _).
(* 0x887e0 .. 0x887f0: a1 = "yes", s7 = val, a0 = s7, the call *)
paj_run_tok RUN HS HJ SHOK Bspan. { b12e_awr. }
b12e_afterc E0 HAE KM.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
prreg HS (Z_to_bv 5 23) Q23.
pmkst HS.
apply (b12_call B TL ASCMP e _ _ _ S_yes B12_R1 _ HE).
+ exact (b12_mid_step B e regs1 memc1 mdc1 _ _ _ HM HJ KM HK).
+ unfold B12_LITS. cbn [In]. tauto.
+ rewrite Q10. exact (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32).
+ rewrite Q11. pose proof b12_lits as (L1 & _ & _ & _ & _ & _ & L50 & _ & _ & _ & _ & _ & _).
  rewrite L1, <- L50. apply (b12_obj OBJ _ 50 HEI); vm_compute; lia.
+ exact Q1.
+ unfold B12_R1, AF_reac_segconf_parse_file. lia.
+ reflexivity.
+ intros regs2 mem2 md2 HM2 HP2 HQ2.
  apply (HR1 e regs2 mem2 md2 HE HM2 HQ2).
  apply (b12_bvr _ _ 23); [reflexivity|]. rewrite (HP2 23 ltac:(unfold acallee_saved; lia)).
  rewrite Q23. exact (b12_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32).
Qed.
End c.

End e.
End f.
End d.
