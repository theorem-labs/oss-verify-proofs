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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 628 of its 672 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac_segconf_parse_file (image A), segment A10a: the fold loop (0x88218) and its exit (0x88438 .. 0x88450).
   Segment A10a's proof, by the G3 walk owner. Form: this unit's lib/A/Prog/trim_t.v / trim_tr.v (a mid-walk
   seed from concrete facts, token runs, inline checks re-seeded at each iteration), after fuzz_command's
   answer_l.v at origin/ossv/recipes 501c0d516c69.
     END  0x88438  a3 = m, s3 = low: check 25 (low[m]) and the store low[m] = 0, then INTENT 0x88450
     LOOP 0x88218  a0 = k, a1 = val + 1, a2 = val[k], s3 = low: the cap test, the fold store low[k], check 17
                   (val[k + 1]) and the back edge. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA
  refuse_c reac_segconf_parse_file_c pf_pieces pf_a10a_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut pcs of A10a as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition A10_SH16 : Z := AF_reac_segconf_parse_file + 0x77c.   (* 0x881f4 check 16 *)
Definition A10_LOOP : Z := AF_reac_segconf_parse_file + 0x7a0.   (* 0x88218 the fold's head *)
Definition A10_END : Z := AF_reac_segconf_parse_file + 0x9c0.    (* 0x88438 low[m] = 0 *)

Definition a10_Bx : sv := SOff 22 0.

(* the environment after a run still agrees with the seed's below its own atoms (trim_k.v tr_ag32 / tr_ag_ew) *)
Lemma a10_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof.
intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia].
Qed.
Lemma a10_ag_ew : forall E0 E (k n : nat) z, env_agree k E0 E -> (n < k)%nat ->
  ew E0 n = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z.
Proof. intros E0 E k n z H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* the two branches of the fold (0x8821c beq a0,a3 and 0x88258 bnez a2) *)
Lemma a10_br_eq : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc.
rewrite branch_eq_U, (U_atom E n v H Hv), (U_lit E z Hz) in Hc. exact Hc.
Qed.
Lemma a10_br_ne0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> negb (v =? 0) = b.
Proof.
intros E n v b H Hv Hc.
rewrite branch_ne_U, (U_atom E n v H Hv), (U_lit E 0 ltac:(lia)) in Hc. exact Hc.
Qed.


(* ---- END 0x88438: a3 = m (atom 13), s3 = low (atom 19), the alias atom 32 = low + m, written ---- *)
Definition ae_regions : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 1 []].
Definition ae_facts : facts :=
mkFacts [ (13%nat, mkAF 0 63 0); (19%nat, PTR 0); (22%nat, mkAF SB SB 0); (32%nat, PTR 0) ]
[] [ (SAlu ALU_ADD (SOff 19 0) (SOff 13 0), SOff 32 0) ].
Definition ae_ss : sstate := mkSS A10_END sr_atoms ae_regions None ae_facts.
Definition ae_SH : list shent := [mkSHE 32 0 1].

(* ---- LOOP 0x88218: a0 = k (10), a1 = val + 1 (11), a2 = val[k] (12), s3 = low (19); the extra atoms
   32 = low + k (written), 33 = val + 1 + k (read), 34 = val[k + 1] ---- *)
Definition al_regions : smem :=
[ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition al_facts : facts :=
mkFacts [ (10%nat, mkAF 0 63 0); (11%nat, PTR 0); (12%nat, mkAF 0 255 0); (19%nat, PTR 0);
          (22%nat, mkAF SB SB 0); (32%nat, PTR 0); (33%nat, PTR 0); (34%nat, mkAF 0 255 0) ]
[] [ (SAlu ALU_ADD (SOff 19 0) (SOff 10 0), SOff 32 0);
     (SAlu ALU_ADD (SOff 11 0) (SOff 10 0), SOff 33 0) ].
Definition al_ss : sstate := mkSS A10_LOOP sr_atoms al_regions None al_facts.
Definition al_SH : list shent := [mkSHE 32 0 1; mkSHE 33 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition a10_E (regs1 : bvmap 5 word) (xs : list word) : env := Eimg (Ereg regs1 xs).

Lemma a10_ew : forall regs1 xs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (a10_E regs1 xs) n = getr regs1 r.
Proof. intros. unfold a10_E. apply ew_Eimg_Ereg_nat. assumption. Qed.

Lemma ae_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc low m,
getr regs1 13 = w64 m -> getr regs1 19 = w64 low -> getr regs1 22 = w64 SB ->
0 <= m <= 63 -> 4096 <= low -> low + 64 <= 140737479966720 ->
apresent (w_H W) memc (low + m) ->
st_ok_pi SEGS VAL (a10_E regs1 [w64 (low + m)]) ae_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A10_END)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc low m H13 H19 H22 Hm Hl1 Hl2 Hp.
set (E := a10_E regs1 [w64 (low + m)]).
assert (E13 : ew E 13 = Z_to_bv 64 m) by (subst E; rewrite (a10_ew regs1 _ 13 13%bv eq_refl); exact H13).
assert (E19 : ew E 19 = Z_to_bv 64 low) by (subst E; rewrite (a10_ew regs1 _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (a10_ew regs1 _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 (low + m))
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
rewrite restrict_mkst_fx. unfold ae_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ae_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E32, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros ov Hov. assert (ov = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
- cbn. tauto.
- split; [|split; [exact I|]].
  + cbn [ae_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E13, E19, E22, E32, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [ae_facts f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 19 low E19), (U_atom E 13 m E13), (U_atom E 32 (low + m) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* a run of the fold writes at most low[k], the one byte of region 32 (answer_l.v al_keep_step) *)
Lemma a10_keep_step : forall (E : env) cs0 cs1 (m0 m m' : word -> option byte) (H : word -> bool) Pz,
  frame_of E [YP09.mkRegion (Some 32%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 33%nat) 0 1 0 0 cs1]
    (mrestrict H m) (mrestrict H m') ->
  bv_unsigned (ew E 32) = Pz ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs0 cs1 m0 m m' H Pz HFr H32 KM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun a' => a' = Pz) HFr);
  [exact (KM a Ha Hn) | | exact Ha | exact Hn].
intros b wlo whi a' Hin Hrr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
  rewrite ?H32 in Hrr; lia.
Qed.

Ltac a10_fold_byte HSn ssn En U32n E12n STMT HWBname cc :=
  let r := eval vm_compute in (nth_error (ss_mem ssn) 0) in
  lazymatch r with
  | Some (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
    lazymatch cs with
    | [YP09.mkChunk 0 (CVal 1 ?ex)] =>
      let HNTH := fresh "HNTH" in
      assert (HNTH : nth_error (ss_mem ssn) 0
         = Some (YP09.mkRegion (Some 32%nat) lo hi wlo whi cs)) by (vm_compute; reflexivity);
      let HW := fresh "HW" in
      pose proof (a10_wbyte En ssn _ _ 32%nat 0%nat lo hi wlo whi cs 0 ex _ HSn HNTH
        ltac:(cbn [In]; tauto) U32n) as HW;
      rewrite Z.add_0_r in HW;
      assert (HWBname : STMT);
      [ rewrite HW; f_equal;
        rewrite <- (a10_fold_arith cc ltac:(lia));
        rewrite !U_SAlu, !U_SOff, !U_SLit, E12n;
        rewrite (unsigned_lit_small cc) by lia;
        cbn [zalu_raw]; unfold zcanon, M64;
        rewrite !Z.add_0_r;
        rewrite (Z.mod_small cc (2 ^ 64)) by lia;
        replace (26 mod 2 ^ 64) with 26 by reflexivity;
        replace (5 mod 2 ^ 64) with 5 by reflexivity;
        change (Z.land 5 63) with 5;
        destruct (Z.ltb_spec ((cc + -65) mod 2 ^ 64) 26) as [Hb|Hb];
        [ replace (1 mod 2 ^ 64) with 1 by reflexivity;
          replace (Z.shiftl 1 5) with 32 by reflexivity;
          replace (32 mod 2 ^ 64) with 32 by reflexivity; reflexivity
        | replace (0 mod 2 ^ 64) with 0 by reflexivity;
          replace (Z.shiftl 0 5) with 0 by reflexivity;
          rewrite !Z.add_0_r; reflexivity ]
      | ]
    end
  end.

Ltac a10_awr AWRh U32x :=
  lazymatch goal with
  | |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in
    change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own)
  end;
  apply AWRh; exact U32x.

Ltac a10_keep KMold KMnew U32x :=
  lazymatch goal with
  | HFrn : frame_of ?Eo _ (mrestrict ?H ?mprev) (mrestrict ?H (ms_mem ?msn)) |- _ =>
    pose proof (a10_keep_step Eo _ _ _ mprev (ms_mem msn) H _ HFrn U32x KMold) as KMnew;
    clear HFrn
  end.

Lemma al_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc low vp1 k c cnext,
getr regs1 10 = w64 k -> getr regs1 11 = w64 vp1 -> getr regs1 12 = w64 c ->
getr regs1 19 = w64 low -> getr regs1 22 = w64 SB ->
0 <= k <= 63 -> 0 <= c <= 255 -> 0 <= cnext <= 255 ->
4096 <= low -> low + 64 <= 140737479966720 -> 4096 <= vp1 -> vp1 + 64 <= 140737479966720 ->
apresent (w_H W) memc (low + k) -> rdW W memc (vp1 + k) = Some cnext ->
(low + k + 1 <= vp1 + k \/ vp1 + k + 1 <= low + k) ->
st_ok_pi SEGS VAL (a10_E regs1 [w64 (low + k); w64 (vp1 + k); w64 cnext]) al_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A10_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc low vp1 k c cnext H10 H11 H12 H19 H22 Hk Hc Hcn Hl1 Hl2 Hv1 Hv2 Hp Hrd Hdis.
set (E := a10_E regs1 [w64 (low + k); w64 (vp1 + k); w64 cnext]).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (subst E; rewrite (a10_ew regs1 _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 vp1) by (subst E; rewrite (a10_ew regs1 _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 c) by (subst E; rewrite (a10_ew regs1 _ 12 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 low) by (subst E; rewrite (a10_ew regs1 _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (a10_ew regs1 _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 (low + k))
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (vp1 + k))
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cnext)
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
rewrite restrict_mkst_fx. unfold al_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold al_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros ov Hov. assert (ov = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E33, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros ov Hov; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi.
    assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc (vp1 + k) cnext Hrd) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E34.
      rewrite !Z.add_0_r, (unsigned_lit_small cnext), (unsigned_lit_small cnext) by lia.
      change (8 * 0) with 0. rewrite Z.shiftr_0_r. subst cnext. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
- unfold al_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E32, E33, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [al_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E10, E11, E12, E19, E22, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [al_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 19 low E19), (U_atom E 10 k E10), (U_atom E 32 (low + k) E32) by lia.
      apply zcanon_id. unfold M64. lia.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 11 vp1 E11), (U_atom E 10 k E10), (U_atom E 33 (vp1 + k) E33) by lia.
      apply zcanon_id. unfold M64. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the geometry of the cut that both runs need *)
Definition a10_geo (v : pfv) (pos : Z) (vp : Z) (val : list Z) : Prop :=
  pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) 2048 /\ off_img (pf_F v pos) 2048 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\
  pf_F v pos + PF_O_BUF <= vp /\ vp + Z.of_nat (length val) < pf_F v pos + PF_O_BUF + 512.

Lemma a10_geo_of : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k,
  a10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k ->
  a10_geo v pos vp val.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
  (HKV & _ & HJ & _).
destruct HKV as ((_ & HFI & _) & _ & _ & (_ & _ & _ & _ & Hvb) & _).
pose proof HFI as (HJ0 & Hly & _).
destruct (a10_frame B LAWS v pos lyc Sc Wc _ _ HJ0 Hly) as (_ & _ & F32 & Fapp & Foff & F4096 & Fc & _).
unfold pf_inb in Hvb.
split; [exact F32|]. split; [exact Fapp|]. split; [exact Foff|]. split; [exact F4096|]. split; [exact Fc|].
split; lia.
Qed.

(* ---- END: check 25 and the store ---- *)
Definition A10_END_stmt (n : nat) : Prop :=
forall v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
a10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc
  (length (r_low val 0 64)) ->
getr regs1 13 = w64 (Z.of_nat (length (r_low val 0 64))) ->
SRr SEGS Wc (cfg_at SEGS (BASE + A10_END) regs1 memc mdc)
  (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).

Lemma a10_end : forall n, H_INTENT B n -> A10_END_stmt n.
Proof.
intros n HINT v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc HM H13.
pose proof (a10_geo_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)
  as (F32 & Fapp & Foff & F4096 & Fc & Hb1 & Hb2).
pose proof HM as (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK & R19).
pose proof HKV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HKVS & HSLB & HRG).
pose proof HFI as (HJ0 & Hly & _ & _ & _ & _ & _ & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (a10_frame B LAWS v pos lyc Sc Wc memc mdc HJ Hly) as (_ & HAR & _ & _ & _ & _ & _ & Fp & _ & _).
assert (Happ : 4096 <= pf_F v pos /\
  (pf_F v pos + 2048 <= kLowShadowBeg \/ (kHighMemBeg <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling)))
  by (unfold in_app, ASAN_CEIL in Fapp; exact Fapp).
assert (R22 : getr regs1 22 = w64 SB).
{ rewrite SB_SHADOW_OFF. rewrite <- (a10_getz regs1 22%bv 22 ltac:(vm_compute; reflexivity)).
  rewrite (HK 22 ltac:(a10_inZ)).
  exact (pf_a5_k.a5_rg_get rX0 _ 22 SHADOW_OFF HRG0 ltac:(cbn [In]; tauto)). }
assert (R19' : getr regs1 19 = w64 (pf_F v pos + PF_O_LOW))
  by (rewrite <- (a10_getz regs1 19%bv 19 ltac:(vm_compute; reflexivity)); exact R19).
set (m := length (r_low val 0 64)) in *.
assert (Hm : 0 <= Z.of_nat m <= 63) by lia.
assert (Hlow1 : 4096 <= pf_F v pos + PF_O_LOW) by (unfold PF_O_LOW; lia).
assert (Hlow2 : pf_F v pos + PF_O_LOW + 64 <= 140737479966720) by (unfold PF_O_LOW; lia).
assert (Hpres : apresent (w_H Wc) memc (pf_F v pos + PF_O_LOW + Z.of_nat m))
  by (apply Fp; unfold PF_O_LOW; lia).
pose proof (ae_entry Wc regs1 memc (pf_F v pos + PF_O_LOW) (Z.of_nat m) H13 R19' R22 Hm Hlow1 Hlow2 Hpres) as HS.
assert (HEI : img_env VAL A_LIM (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]))
  by (unfold a10_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)])
  (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]))
  by (split; [intros nn Hn; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E22 : ew (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]) 22 = Z_to_bv 64 SB)
  by (rewrite (a10_ew regs1 _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]) 32
  = Z_to_bv 64 (pf_F v pos + PF_O_LOW + Z.of_nat m))
  by (unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
(* the shadow entry: low[m]'s cell is one of low's eight, and they are 0 *)
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_LOW + Z.of_nat m) 1).
{ intros x Hx. assert (x = pf_F v pos + PF_O_LOW + Z.of_nat m) as -> by lia. exists 0. split; [|left; reflexivity].
  rewrite (a10_sh_of v pos (pf_F v pos + PF_O_LOW + Z.of_nat m) F32 ltac:(unfold PF_O_LOW; lia)).
  replace (pf_F v pos + PF_O_LOW + Z.of_nat m - pf_F v pos) with (Z.of_nat m + 80 * 8)
    by (unfold PF_O_LOW; lia).
  rewrite Z_div_plus by lia.
  replace (pf_SH v pos + (Z.of_nat m / 8 + 80)) with (pf_SH v pos + 80 + Z.of_nat m / 8) by lia.
  apply Z0. pose proof (Z.div_mod (Z.of_nat m) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.of_nat m) 8 ltac:(lia)). lia. }
assert (SHOK : sh_ok SEGS a10_Bx ae_SH (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)])
  (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, ae_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc _ a10_Bx 32%nat
    (pf_F v pos + PF_O_LOW + Z.of_nat m) 1 (pf_F v pos + PF_O_LOW + Z.of_nat m) 0 1 HRA);
  [ unfold a10_Bx; rewrite (U_atom _ 22 SB E22) by (unfold SB; lia); reflexivity
  | apply (U_atom _ 32 _ E32); lia | lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. unfold PF_O_LOW in *. lia. }
assert (E19o : ew (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]) 19
  = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
  by (rewrite (a10_ew regs1 _ 19 19%bv eq_refl); exact R19').
revert HS SHOK HEI HA0 E22 E32 E19o.
generalize (a10_E regs1 [w64 (pf_F v pos + PF_O_LOW + Z.of_nat m)]) as E0.
intros E0 HS SHOK HEI HA0 E22 E32 E19o.
assert (U32 : bv_unsigned (ew E0 32) = pf_F v pos + PF_O_LOW + Z.of_nat m)
  by (rewrite E32; apply unsigned_lit_small; unfold PF_O_LOW; lia).
(* 0x88438 .. 0x8844c: check 25, the store, then INTENT *)
pose proof (env_agree_refl 35 E0) as HAE.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_INTENT.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 32%nat) (b := pf_F v pos + PF_O_LOW + Z.of_nat m);
    [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite Hly. change (fs_frame_bytes 5) with 2048.
  unfold pf_F, PF_O_LOW in *. lia. }
lazymatch goal with
| HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
  assert (HAE1 : env_agree 35 E0 En) by (env_agree_chain HAE);
  assert (U32n : bv_unsigned (ew En 32) = pf_F v pos + PF_O_LOW + Z.of_nat m)
    by (rewrite (a10_ag_ew E0 En 35 32 _ HAE1 ltac:(lia) E32); apply unsigned_lit_small;
        unfold PF_O_LOW; lia);
  assert (E19n : ew En 19 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
    by (exact (a10_ag_ew E0 En 35 19 _ HAE1 ltac:(lia) E19o));
  assert (HNTH : nth_error (ss_mem ssn) 0
     = Some (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]))
    by (vm_compute; reflexivity);
  pose proof (a10_wbyte En ssn _ _ 32%nat 0%nat 0 1 0 1 _ 0 (SLit 0) _ HSn HNTH
    ltac:(cbn [In]; tauto) U32n) as HW;
  assert (HFA : forallb (fun r : bv 5 =>
     sv_eqb (sr_get (ss_regs ssn) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
    by (vm_compute; reflexivity);
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ A10_KEPT HSn
    (a10_ag32 _ _ E0 En 35 ltac:(lia) HA0 HAE1) HFA) as HKr
end.
cbn [ms_regs restrict] in HKr.
assert (KS : forall a, 0 <= a < 2 ^ 64 -> a <> pf_F v pos + PF_O_LOW + Z.of_nat m ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms)
    (fun a' => a' = pf_F v pos + PF_O_LOW + Z.of_nat m) HFr); [|exact Ha | exact Hne].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U32 in Hrr; lia. }
assert (HW0 : rdW Wc (ms_mem ms) (pf_F v pos + PF_O_LOW + Z.of_nat m) = Some 0).
{ rewrite Z.add_0_r in HW. rewrite HW. f_equal; try reflexivity. }
prreg HS (19%bv : bv 5) N19.
first [rewrite E19n in N19 | rewrite E19o in N19].
assert (R19n : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_LOW))
  by (rewrite (a10_getz _ 19%bv 19 ltac:(vm_compute; reflexivity)); exact N19).
pmkst HS.
apply (HINT v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ cf nm o ln d gi vp val).
apply (a10_intent B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
  (ms_regs ms) (ms_mem ms) _); [|exact HW0].
exact (a10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
  regs1 memc mdc (length (r_low val 0 64)) (ms_regs ms) (ms_mem ms) _ (length (r_low val 0 64))
  HM HJ KS (or_introl eq_refl) Hkl Hk63 (a10_kept_keep regs1 (ms_regs ms) HKr) R19n).
Qed.

(* ---- LOOP 0x88218: the fold's head, a0 = k, a1 = val + 1, a2 = val[k] <> 0 ---- *)
Definition A10_LOOP_at (n k : nat) : Prop :=
forall v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
a10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k ->
(k < length val)%nat ->
getr regs1 10 = w64 (Z.of_nat k) ->
getr regs1 11 = w64 (vp + 1) ->
getr regs1 12 = w64 (nth k val 0) ->
SRr SEGS Wc (cfg_at SEGS (BASE + A10_LOOP) regs1 memc mdc)
  (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).

Lemma a10_loop_step : forall n, A10_END_stmt n -> forall q,
  (forall q', (q' < q)%nat -> forall k, (63 - k = q')%nat -> A10_LOOP_at n k) ->
  forall k, (63 - k = q)%nat -> A10_LOOP_at n k.
Proof.
intros n HEND q IHq k Hq v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc
  HM Hklen H10 H11 H12.
pose proof (a10_geo_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)
  as (F32 & Fapp & Foff & F4096 & Fc & Hb1 & Hb2).
pose proof HM as (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK & R19).
pose proof HKV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HKVS & HSLB & HRG).
pose proof HFI as (HJ0 & Hly & _ & _ & _ & _ & _ & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (a10_frame B LAWS v pos lyc Sc Wc memc mdc HJ Hly) as (_ & HAR & _ & _ & _ & _ & _ & Fp & _ & _).
assert (Happ : 4096 <= pf_F v pos /\
  (pf_F v pos + 2048 <= kLowShadowBeg \/ (kHighMemBeg <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling)))
  by (unfold in_app, ASAN_CEIL in Fapp; exact Fapp).
destruct HKVS as (Hsplit & Hks & Hkb & Hvs & Hvb).
pose proof Hvs as ((HVZ & NZ) & _).
assert (VR : forall i, (i < length val)%nat -> 0 <= nth i val 0 < 256).
{ intros i Hi. pose proof (HVZ i ltac:(rewrite length_app; cbn [length]; lia)) as E.
  rewrite app_nth1 in E by exact Hi. destruct (aview_byte SEGS _ _ _ _ E) as (_ & _ & _ & Hr). exact Hr. }
pose proof (a10_r_low64_len val NZ) as RLL.
assert (R22 : getr regs1 22 = w64 SB).
{ rewrite SB_SHADOW_OFF. rewrite <- (a10_getz regs1 22%bv 22 ltac:(vm_compute; reflexivity)).
  rewrite (HK 22 ltac:(a10_inZ)).
  exact (pf_a5_k.a5_rg_get rX0 _ 22 SHADOW_OFF HRG0 ltac:(cbn [In]; tauto)). }
assert (R19' : getr regs1 19 = w64 (pf_F v pos + PF_O_LOW))
  by (rewrite <- (a10_getz regs1 19%bv 19 ltac:(vm_compute; reflexivity)); exact R19).
unfold pf_inb, PF_O_BUF in Hvb.
(* the byte after val[k]: val[k + 1], or the NUL when k + 1 = |val| *)
set (cn := nth (S k) (val ++ [0]) 0) in *.
assert (HCN : rdW Wc memc (vp + 1 + Z.of_nat k) = Some cn).
{ replace (vp + 1 + Z.of_nat k) with (vp + Z.of_nat (S k)) by lia.
  rewrite KM; [exact (HVZ (S k) ltac:(rewrite length_app; cbn [length]; lia))|].
  split; [unfold PF_O_BUF in *; lia|].
  apply (a10_nD_in v pos _ F32 Fapp Fc). left. unfold PF_O_BUF, PF_O_LOW in *. lia. }
assert (HCNr : 0 <= cn <= 255).
{ destruct (aview_byte SEGS _ _ _ _ HCN) as (_ & _ & _ & Hr). lia. }
assert (HCr : 0 <= nth k val 0 <= 255) by (pose proof (VR k Hklen); lia).
assert (Hlow1 : 4096 <= pf_F v pos + PF_O_LOW) by (unfold PF_O_LOW; lia).
assert (Hlow2 : pf_F v pos + PF_O_LOW + 64 <= 140737479966720) by (unfold PF_O_LOW; lia).
assert (Hv1 : 4096 <= vp + 1) by (unfold PF_O_BUF in *; lia).
assert (Hv2 : vp + 1 + 64 <= 140737479966720) by (unfold PF_O_BUF in *; lia).
assert (Hpres : apresent (w_H Wc) memc (pf_F v pos + PF_O_LOW + Z.of_nat k))
  by (apply Fp; unfold PF_O_LOW; lia).
assert (Hdis : pf_F v pos + PF_O_LOW + Z.of_nat k + 1 <= vp + 1 + Z.of_nat k \/
               vp + 1 + Z.of_nat k + 1 <= pf_F v pos + PF_O_LOW + Z.of_nat k)
  by (right; unfold PF_O_LOW, PF_O_BUF in *; lia).
pose proof (al_entry Wc regs1 memc (pf_F v pos + PF_O_LOW) (vp + 1) (Z.of_nat k) (nth k val 0) cn
  H10 H11 H12 R19' R22 ltac:(lia) HCr HCNr Hlow1 Hlow2 Hv1 Hv2 Hpres HCN Hdis) as HS.
set (XS := [w64 (pf_F v pos + PF_O_LOW + Z.of_nat k); w64 (vp + 1 + Z.of_nat k); w64 cn]) in *.
assert (HEI : img_env VAL A_LIM (a10_E regs1 XS)) by (unfold a10_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 XS) (a10_E regs1 XS))
  by (split; [intros nn Hn; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E10 : ew (a10_E regs1 XS) 10 = Z_to_bv 64 (Z.of_nat k))
  by (rewrite (a10_ew regs1 _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew (a10_E regs1 XS) 11 = Z_to_bv 64 (vp + 1))
  by (rewrite (a10_ew regs1 _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew (a10_E regs1 XS) 12 = Z_to_bv 64 (nth k val 0))
  by (rewrite (a10_ew regs1 _ 12 12%bv eq_refl); exact H12).
assert (E19o : ew (a10_E regs1 XS) 19 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
  by (rewrite (a10_ew regs1 _ 19 19%bv eq_refl); exact R19').
assert (E22 : ew (a10_E regs1 XS) 22 = Z_to_bv 64 SB)
  by (rewrite (a10_ew regs1 _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew (a10_E regs1 XS) 32 = Z_to_bv 64 (pf_F v pos + PF_O_LOW + Z.of_nat k))
  by (unfold a10_E, XS; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew (a10_E regs1 XS) 33 = Z_to_bv 64 (vp + 1 + Z.of_nat k))
  by (unfold a10_E, XS; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew (a10_E regs1 XS) 34 = Z_to_bv 64 cn)
  by (unfold a10_E, XS; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
(* the two shadow entries: low[k] and val[k + 1], both cells of the frame *)
pose proof (a10_fsh_low B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
  regs1 memc mdc k HM) as FSH.
assert (HRA32 : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_LOW + Z.of_nat k) 1).
{ intros x Hx. assert (x = pf_F v pos + PF_O_LOW + Z.of_nat k) as -> by lia.
  exists 0. split; [|left; reflexivity].
  rewrite (a10_sh_of v pos (pf_F v pos + PF_O_LOW + Z.of_nat k) F32 ltac:(unfold PF_O_LOW; lia)).
  replace (pf_F v pos + PF_O_LOW + Z.of_nat k - pf_F v pos) with (Z.of_nat k + 80 * 8)
    by (unfold PF_O_LOW; lia).
  rewrite Z_div_plus by lia.
  pose proof (Z.div_mod (Z.of_nat k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.of_nat k) 8 ltac:(lia)).
  rewrite (FSH (Z.of_nat k / 8 + 80) ltac:(lia)). f_equal. apply a10_shb_lowcell. lia. }
assert (HRA33 : range_addressable (rdW Wc memc) SHADOW_OFF (vp + 1 + Z.of_nat k) 1).
{ intros x Hx. assert (x = vp + 1 + Z.of_nat k) as -> by lia.
  exists 0. split; [|left; reflexivity].
  rewrite (a10_sh_of v pos (vp + 1 + Z.of_nat k) F32 ltac:(unfold PF_O_BUF in *; lia)).
  pose proof (Z.div_mod (vp + 1 + Z.of_nat k - pf_F v pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (vp + 1 + Z.of_nat k - pf_F v pos) 8 ltac:(lia)).
  rewrite (FSH ((vp + 1 + Z.of_nat k - pf_F v pos) / 8) ltac:(unfold PF_O_BUF in *; lia)).
  f_equal. apply a10_shb_bufcell. unfold PF_O_BUF in *. lia. }
assert (SHOK : sh_ok SEGS a10_Bx al_SH (a10_E regs1 XS) (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, al_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc _ a10_Bx 32%nat
      (pf_F v pos + PF_O_LOW + Z.of_nat k) 1 (pf_F v pos + PF_O_LOW + Z.of_nat k) 0 1 HRA32);
    [ unfold a10_Bx; rewrite (U_atom _ 22 SB E22) by (unfold SB; lia); reflexivity
    | apply (U_atom _ 32 _ E32); unfold PF_O_LOW; lia | lia | lia |].
    intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. unfold PF_O_LOW in *. lia.
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc _ a10_Bx 33%nat
      (vp + 1 + Z.of_nat k) 1 (vp + 1 + Z.of_nat k) 0 1 HRA33);
    [ unfold a10_Bx; rewrite (U_atom _ 22 SB E22) by (unfold SB; lia); reflexivity
    | apply (U_atom _ 33 _ E33); unfold PF_O_BUF in *; lia | lia | lia |].
    intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. unfold PF_O_BUF in *. lia. }
revert HS SHOK HEI HA0 E10 E11 E12 E19o E22 E32 E33 E34.
generalize (a10_E regs1 XS) as E0.
intros E0 HS SHOK HEI HA0 E10 E11 E12 E19o E22 E32 E33 E34.
assert (U32 : bv_unsigned (ew E0 32) = pf_F v pos + PF_O_LOW + Z.of_nat k)
  by (rewrite E32; apply unsigned_lit_small; unfold PF_O_LOW; lia).
assert (U33 : bv_unsigned (ew E0 33) = vp + 1 + Z.of_nat k)
  by (rewrite E33; apply unsigned_lit_small; unfold PF_O_BUF in *; lia).
pose proof (env_agree_refl 35 E0) as HAE.
(* the writes of a pass: low[k], the one byte of region 32 *)
assert (AWR : forall (Ex : env) cs0 cs1 stk spx fp b0 bc fr0,
  bv_unsigned (ew Ex 32) = pf_F v pos + PF_O_LOW + Z.of_nat k ->
  awr_ok SEGS B Ex [YP09.mkRegion (Some 32%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 33%nat) 0 1 0 0 cs1]
    stk spx fp b0 bc fr0 lyc [(5, pos)]).
{ intros Ex cs0 cs1 stk spx fp b0 bc fr0 U32x.
  eapply awr_ok_cons_gen with (n := 32%nat) (b := pf_F v pos + PF_O_LOW + Z.of_nat k);
    [reflexivity | exact U32x | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite Hly. change (fs_frame_bytes 5) with 2048.
  unfold pf_F, PF_O_LOW in *. lia. }
assert (KM0 : forall a, 0 <= a < 2 ^ 64 -> a <> pf_F v pos + PF_O_LOW + Z.of_nat k ->
  rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
(* 0x88218 .. 0x8821c: a3 = 63, the cap test *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a10_awr AWR U32. }
a10_keep KM0 KM1 U32.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* k = 63: the fold is full, j 0x88438 *)
  pose proof (a10_br_eq E0 10 (Z.of_nat k) 63 _ E10 ltac:(lia) ltac:(lia) Hc) as Hk63e.
  apply Z.eqb_eq in Hk63e. clear Hc.
  assert (Hmk : length (r_low val 0 64) = k) by (rewrite RLL; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A10_END.
  { a10_awr AWR U32. }
  a10_keep KM1 KM2 U32.
  lazymatch goal with
  | HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
    assert (HAE1 : env_agree 35 E0 En) by (env_agree_chain HAE);
    assert (HFA : forallb (fun r : bv 5 =>
       sv_eqb (sr_get (ss_regs ssn) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
      by (vm_compute; reflexivity);
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ A10_KEPT HSn
      (a10_ag32 _ _ E0 En 35 ltac:(lia) HA0 HAE1) HFA) as HKr;
    cbn [ms_regs restrict] in HKr;
    assert (E19n : ew En 19 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
      by (exact (a10_ag_ew E0 En 35 19 _ HAE1 ltac:(lia) E19o));
    prreg HSn (13%bv : bv 5) N13;
    prreg HSn (19%bv : bv 5) N19;
    assert (R19n : getr (ms_regs msn) (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_LOW))
      by (rewrite (a10_getz _ 19%bv 19 ltac:(vm_compute; reflexivity)), N19;
          first [exact E19o | exact E19n | reflexivity]);
    pmkst HSn;
    apply (HEND v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
      (ms_regs msn) (ms_mem msn) _);
    [ rewrite Hmk;
      exact (a10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
        regs1 memc mdc k (ms_regs msn) (ms_mem msn) _ k HM HJ KM2 (or_introl eq_refl) Hkl Hk63
        (a10_kept_keep regs1 (ms_regs msn) HKr) R19n)
    | rewrite Hmk, N13; unfold w64; f_equal; lia ]
  end.
- (* k < 63: the fold stores low[k], then check 17 and the latch *)
  pose proof (a10_br_eq E0 10 (Z.of_nat k) 63 _ E10 ltac:(lia) ltac:(lia) Hc) as Hk63n.
  apply Z.eqb_neq in Hk63n. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { a10_awr AWR U32. }
  a10_keep KM1 KM2 U32.
  lazymatch goal with
  | HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
    assert (HAE1 : env_agree 35 E0 En) by (env_agree_chain HAE);
    assert (E34n : ew En 34 = Z_to_bv 64 cn)
      by (exact (a10_ag_ew E0 En 35 34 _ HAE1 ltac:(lia) E34))
  end.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* val[k + 1] <> 0: the back edge to 0x88218 *)
    pose proof (a10_br_ne0 _ 34 cn _ E34n ltac:(lia) Hc) as Hcn.
    apply Bool.negb_true_iff, Z.eqb_neq in Hcn. clear Hc.
    assert (HSk : (S k < length val)%nat).
    { destruct (Nat.lt_ge_cases (S k) (length val)) as [Hl|Hl]; [exact Hl|].
      exfalso. apply Hcn. unfold cn. rewrite app_nth2 by lia.
      assert (S k = length val) as Heq by lia. rewrite Heq, Nat.sub_diag. reflexivity. }
    assert (Hcnv : cn = nth (S k) val 0) by (unfold cn; rewrite app_nth1 by exact HSk; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A10_LOOP.
    { a10_awr AWR U32. }
    a10_keep KM2 KM3 U32.
    lazymatch goal with
    | HSn : st_ok_pi _ _ ?En2 ?ssn2 (restrict _ ?msn2) |- _ =>
      assert (HAE2 : env_agree 35 E0 En2) by (env_agree_chain HAE);
      assert (HFA2 : forallb (fun r : bv 5 =>
         sv_eqb (sr_get (ss_regs ssn2) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
        by (vm_compute; reflexivity);
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ A10_KEPT HSn
        (a10_ag32 _ _ E0 En2 35 ltac:(lia) HA0 HAE2) HFA2) as HKr2;
      cbn [ms_regs restrict] in HKr2;
      assert (E19m : ew En2 19 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
        by (exact (a10_ag_ew E0 En2 35 19 _ HAE2 ltac:(lia) E19o));
      assert (E10m : ew En2 10 = Z_to_bv 64 (Z.of_nat k))
        by (exact (a10_ag_ew E0 En2 35 10 _ HAE2 ltac:(lia) E10));
      assert (E11m : ew En2 11 = Z_to_bv 64 (vp + 1))
        by (exact (a10_ag_ew E0 En2 35 11 _ HAE2 ltac:(lia) E11));
      assert (U32n : bv_unsigned (ew En2 32) = pf_F v pos + PF_O_LOW + Z.of_nat k)
        by (rewrite (a10_ag_ew E0 En2 35 32 _ HAE2 ltac:(lia) E32); apply unsigned_lit_small;
            unfold PF_O_LOW; lia);
      assert (E12m : ew En2 12 = Z_to_bv 64 (nth k val 0))
        by (exact (a10_ag_ew E0 En2 35 12 _ HAE2 ltac:(lia) E12));
      a10_fold_byte HSn ssn2 En2 U32n E12m
        (rdW Wc (ms_mem msn2) (pf_F v pos + PF_O_LOW + Z.of_nat k) = Some (lower (nth k val 0)))
        HWB (nth k val 0);
      assert (E34m : ew En2 34 = Z_to_bv 64 cn)
        by (exact (a10_ag_ew E0 En2 35 34 _ HAE2 ltac:(lia) E34));
      prreg HSn (10%bv : bv 5) M10;
      prreg HSn (11%bv : bv 5) M11;
      prreg HSn (12%bv : bv 5) M12;
      prreg HSn (19%bv : bv 5) M19;
      pmkst HSn;
      apply (IHq (63 - S k)%nat ltac:(lia) (S k) eq_refl v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi
        kp vp key val (ms_regs msn2) (ms_mem msn2) _);
      [ exact (a10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
          regs1 memc mdc k (ms_regs msn2) (ms_mem msn2) _ (S k) HM HJ KM3
          (or_intror (conj eq_refl HWB)) ltac:(lia) ltac:(lia)
          (a10_kept_keep regs1 (ms_regs msn2) HKr2)
          ltac:(rewrite (a10_getz _ 19%bv 19 ltac:(vm_compute; reflexivity)), M19; exact E19o))
      | lia
      | rewrite M10, E10, (unsigned_lit_small (Z.of_nat k)) by lia; unfold w64; f_equal; lia
      | rewrite M11; exact E11
      | rewrite M12, E34, Hcnv; reflexivity ]
    end.
  + (* val[k + 1] = 0: the fold ends, j 0x88438 *)
    pose proof (a10_br_ne0 _ 34 cn _ E34n ltac:(lia) Hc) as Hcn.
    apply Bool.negb_false_iff, Z.eqb_eq in Hcn. clear Hc.
    assert (HSk : S k = length val).
    { destruct (Nat.lt_ge_cases (S k) (length val)) as [Hl|Hl]; [|lia].
      exfalso. apply NZ.
      assert (Hx : nth (S k) val 0 = 0)
        by (unfold cn in Hcn; rewrite app_nth1 in Hcn by exact Hl; exact Hcn).
      rewrite <- Hx. apply nth_In. exact Hl. }
    assert (Hmk : length (r_low val 0 64) = S k) by (rewrite RLL; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A10_END.
    { a10_awr AWR U32. }
    a10_keep KM2 KM3 U32.
    lazymatch goal with
    | HSn : st_ok_pi _ _ ?En2 ?ssn2 (restrict _ ?msn2) |- _ =>
      assert (HAE2 : env_agree 35 E0 En2) by (env_agree_chain HAE);
      assert (HFA2 : forallb (fun r : bv 5 =>
         sv_eqb (sr_get (ss_regs ssn2) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
        by (vm_compute; reflexivity);
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ A10_KEPT HSn
        (a10_ag32 _ _ E0 En2 35 ltac:(lia) HA0 HAE2) HFA2) as HKr2;
      cbn [ms_regs restrict] in HKr2;
      assert (E19m : ew En2 19 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
        by (exact (a10_ag_ew E0 En2 35 19 _ HAE2 ltac:(lia) E19o));
      assert (E10m : ew En2 10 = Z_to_bv 64 (Z.of_nat k))
        by (exact (a10_ag_ew E0 En2 35 10 _ HAE2 ltac:(lia) E10));
      assert (U32n : bv_unsigned (ew En2 32) = pf_F v pos + PF_O_LOW + Z.of_nat k)
        by (rewrite (a10_ag_ew E0 En2 35 32 _ HAE2 ltac:(lia) E32); apply unsigned_lit_small;
            unfold PF_O_LOW; lia);
      assert (E12m : ew En2 12 = Z_to_bv 64 (nth k val 0))
        by (exact (a10_ag_ew E0 En2 35 12 _ HAE2 ltac:(lia) E12));
      a10_fold_byte HSn ssn2 En2 U32n E12m
        (rdW Wc (ms_mem msn2) (pf_F v pos + PF_O_LOW + Z.of_nat k) = Some (lower (nth k val 0)))
        HWB (nth k val 0);
      prreg HSn (13%bv : bv 5) M13;
      prreg HSn (19%bv : bv 5) M19;
      pmkst HSn;
      apply (HEND v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
        (ms_regs msn2) (ms_mem msn2) _);
      [ rewrite Hmk;
        exact (a10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
          regs1 memc mdc k (ms_regs msn2) (ms_mem msn2) _ (S k) HM HJ KM3
          (or_intror (conj eq_refl HWB)) ltac:(lia) ltac:(lia)
          (a10_kept_keep regs1 (ms_regs msn2) HKr2)
          ltac:(rewrite (a10_getz _ 19%bv 19 ltac:(vm_compute; reflexivity)), M19; exact E19o))
      | rewrite Hmk, M13, E10, (unsigned_lit_small (Z.of_nat k)) by lia;
        unfold w64; f_equal; lia ]
    end.
Qed.

Lemma a10_loop : forall n, A10_END_stmt n -> forall k, A10_LOOP_at n k.
Proof.
intros n HE.
assert (ALL : forall q k, (63 - k <= q)%nat -> A10_LOOP_at n k).
{ induction q as [|q IHq]; intros k0 Hk0.
  - apply (a10_loop_step n HE (63 - k0)%nat); [intros q' Hq' k1 Hk1; exfalso; lia | reflexivity].
  - apply (a10_loop_step n HE (63 - k0)%nat); [intros q' Hq' k1 Hk1 | reflexivity].
    apply IHq. lia. }
intros k. exact (ALL (63 - k)%nat k (le_n _)).
Qed.
End e.
End f.
End d.
