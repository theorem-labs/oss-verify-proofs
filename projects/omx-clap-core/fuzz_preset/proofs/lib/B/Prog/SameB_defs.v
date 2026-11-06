(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the walk of same (fuzz_preset.c:65-86) at image B' (asan-ubsan #102 pin
   d663f82d7f48, unstripped twin c90d4fa54d43), against the batch kit's text tsame_specX (lib/A/PRH_FnEx.v :353 at the cut
   7cdbb61b5fa0, with its guarded live-stack premise; SameB_walk.v's same_holds_B), over
   the whole-program listing B_prog_listing / PI_prog_B (lib/B/Listing_prog.v c97cc46b3e13, PAImg_prog.v 15fab93fe702):
   same is B_prog_sigma AS_same, 252 instructions, frame 160 (neutral listing, the internal file same.fuzz_preset.asan-ubsan.s, a work
   file outside the tree). This file: the image numbers, the computed segment states, the run tactics, the loop's
   canonical state and the value lemmas of the checks.
   PORT. The segment structure is the image-A walk's (h-hpreset-7's slice S9, lib/A/Prog/Wsame.v at
   origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2): entry (both tags, both n fields), dispatch, number arm,
   string arm, container arm, the item loop in canonical form (head / key / kids) by induction on the items left, and
   the recursive call through the induction hypothesis at nesting n - 1. B' differs from A in register allocation,
   block order (the string arm and the bcmp call sit after the loop), the loop counter (B' counts i UP in s3, with
   8 i in s10 and 56 i in s11, and re-reads a->type and a->n each item), the frame (160, with six spills: 8(sp) =
   (a & 7) + 3, 40(sp) = a + 32, 32(sp) its shadow cell, 24(sp) = b + 32, 16(sp) its shadow cell, 48(sp) = a + 24), s0 = a
   across the recursive call (the STOP), and the UBSan checks below.
   THE UBSan / ASan CHECK BRANCHES (every UBSan check jumps to the one `unimp` at SMB_AT 0x374; every ASan check to an
   __asan_report_* stub). NOT TAKEN, each by the run's facts inside the token runner, or by a named lemma:
   - entry 0x38 `beqz a0`, 0x48 `bnez (a & 7)`, 0x68 `beqz s6`, 0x70 `bnez (b & 7)`: atoms 10 / 11 carry
     [4096, 2 ^ 47 - 56], alignment 3 (smb_fs0); decided in the run.
   - the ASan checks of a, b and their fields, and of the key slots: the shadow entries (shent) of the two roots' 56
     bytes (smb_SH) and of each slot (SameB_walk.v smb_slot_shent); decided in the run.
   - the key part (object, item i; the slot keys + 8 i rebound to a fresh atom by smb_rebind): 0x1e8 `bltu a0, a1`
     (slot < keys) by the two atoms' values; 0x1ec-0x1fc the null xor and `beqz a1` by the fact on the keys atom
     (decided in the run); 0x208 `bnez ((8 i + keys) & 7)` by smb_U_and7 (keys is a 16-aligned block of Lam); the same
     four at 0x234-0x254 for b's keys.
   - the kids part (item i): 0x2a0 the null xor (decided in the run), 0x2a4 `bltu a2, a0` (kids + 56 i < kids) by
     smb_U_add_mul56, 0x2bc `bnez` of the mulh overflow test of i * 56 by smb_U_mulh56; 0x2d0 `bltu a1, a2` for b's
     kids by smb_U_add_mul56, 0x2e0 its null xor (decided in the run).
   Numerals: SMB_AT offsets are LENGTHs (byte offsets inside the 1008-byte body, from the neutral listing); 160
   (LENGTH: the frame), 56 / 8 / 40 / 32 / 24 / 16 (LENGTH: struct pj, its fields, the key stride), 3 / 4 / 6 / 5
   (WORD: the tags of number / string / object / array), 2 ^ 25 / 2 ^ 28 / 2 ^ 30 (DERIVED: bounds of i, 8 i, 56 i from
   cf_malloc_max + 15 <= 2 ^ 30, YG08cf.cf_malloc_max_bound), 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 / 4096 (DERIVED:
   address-space and word bounds), 7 / 63 (WORD: the check masks). No ADDRESS: every image number is a B_prog_sigma /
   B_prog_val term of the listing (port_addr_check: 0 address numerals). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YG0scf YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import SameB_kit SameB_memA SameB_memB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the image numbers, all from the listing ---- *)
(* a pc inside the body of same, by its byte offset from the entry *)
Definition SMB_AT (o : Z) : Z := B_prog_sigma AS_same + o.
Definition SMB_GOT : Z := B_prog_val (A_OBJ 0).
Definition SMB_CELL : Z := B_prog_val (A_OBJ 12).
Definition SMB_STRCMP : Z := B_prog_sigma AS___wrap_strcmp.
Definition SMB_BCMP : Z := B_prog_sigma AS___wrap_bcmp.
Lemma smb_obj_bounds : 4096 <= SMB_GOT /\ SMB_GOT + 8 <= SMB_CELL /\ SMB_CELL + 8 <= 2 ^ 32.
Proof.
unfold SMB_GOT, SMB_CELL.
let g := eval vm_compute in (B_prog_val (A_OBJ 0)) in change (B_prog_val (A_OBJ 0)) with g.
let c := eval vm_compute in (B_prog_val (A_OBJ 12)) in change (B_prog_val (A_OBJ 12)) with c.
lia.
Qed.
Lemma smb_pc_bounds : 4096 <= B_prog_sigma AS_same /\ B_prog_sigma AS_same + 0x400 < 2 ^ 32 /\
  4096 <= SMB_STRCMP < 2 ^ 32 /\ 4096 <= SMB_BCMP < 2 ^ 32.
Proof.
unfold SMB_AT, SMB_STRCMP, SMB_BCMP.
let g := eval vm_compute in (B_prog_sigma AS_same) in change (B_prog_sigma AS_same) with g.
let g := eval vm_compute in (B_prog_sigma AS___wrap_strcmp) in change (B_prog_sigma AS___wrap_strcmp) with g.
let g := eval vm_compute in (B_prog_sigma AS___wrap_bcmp) in change (B_prog_sigma AS___wrap_bcmp) with g.
lia.
Qed.

(* ---- the symbolic entry state: the frame, the .got slot of the shadow base and the base cell (atom 32 = the shadow
   offset); the facts on sp (atom 2), pa (atom 10), pb (atom 11) and the shadow offset ---- *)
Definition smb_got_r : YP09.region :=
  YP09.mkRegion None SMB_GOT (SMB_GOT + 8) 0 0 [YP09.mkChunk SMB_GOT (CVal 8 (SLit SMB_CELL))].
Definition smb_cell_r : YP09.region :=
  YP09.mkRegion None SMB_CELL (SMB_CELL + 8) 0 0 [YP09.mkChunk SMB_CELL (CVal 8 (SOff 32 0))].
Definition smb_fs0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 56) 3);
  (11%nat, mkAF 4096 (2 ^ 47 - 56) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition smb_ss0 : sstate := mkSS (SMB_AT 0) sr_atoms [smbk_fstk 160; smb_got_r; smb_cell_r] None smb_fs0.
Definition smb_SH : list shent := [mkSHE 10 0 56; mkSHE 11 0 56].
Definition smb_Bx : sv := SOff 32 0.

(* ---- the token runner's states, by computation: one run, a hand load into a fresh atom, a branch arm. The walk's
   segment states are these runs from the entry state, so no state is written by hand except the loop's canonical
   one (smb_ssL below) ---- *)
Definition smb_prun (SH : list shent) (ss : sstate) :=
  sym_runN_tok rsegs B_prog_tbl (run_K 0 smb_Bx SH ss) smb_Bx BAND_SPAN SH YP03.FUEL ss.
Definition smb_prun_to (SH : list shent) (stop : Z) (ss : sstate) :=
  sym_run_toN_tok rsegs B_prog_tbl (run_K 0 smb_Bx SH ss) smb_Bx BAND_SPAN SH YP03.FUEL stop ss.
Definition smb_pfin (r : shst * trun_status) : sstate := sh_ss (fst r).
Definition smb_phl (SH : list shent) (r : shst * trun_status) (rd : bv 5) : sstate :=
  let ss := smb_pfin r in set_regs_pc ss [(rd, SOff (run_K 0 smb_Bx SH ss) 0)] (ss_pc ss + 4).
Definition smb_pbr (r : shst * trun_status) (tk : bool) : sstate :=
  match snd r with
  | TS_stopped (SR_branch c a b) => add_cond (smb_pfin r) (mkAC (if tk then c else neg_bc c) a b)
  | _ => smb_pfin r
  end.
(* entry: both tags (atoms 33 / 34), the tag compare *)
Definition smb_r1 := smb_prun smb_SH smb_ss0.
Definition smb_r2 := smb_prun smb_SH (smb_phl smb_SH smb_r1 12%bv).
Definition smb_r3 := smb_prun smb_SH (smb_phl smb_SH smb_r2 10%bv).
(* tags equal: both n fields (atoms 35 / 36), the n compare *)
Definition smb_r4 := smb_prun smb_SH (smb_pbr smb_r3 false).
Definition smb_r5 := smb_prun smb_SH (smb_phl smb_SH smb_r4 13%bv).
Definition smb_r6 := smb_prun smb_SH (smb_phl smb_SH smb_r5 10%bv).
(* n equal: the dispatch branch at SMB_AT 0xcc `bgeu s1, a0` (s1 = 1, a0 = tag - 5) *)
Definition smb_ssD : sstate := Eval vm_compute in smb_pfin (smb_prun smb_SH (smb_pbr smb_r6 false)).
(* the container arm's first branch, SMB_AT 0x15c `beqz a3` (a3 = n) *)
Definition smb_rC := smb_prun smb_SH (add_cond smb_ssD (mkAC BC_GEU (SLit 1) (SOff 33 (-5)))).
Definition smb_ssC : sstate := Eval vm_compute in smb_pfin smb_rC.
(* not a container: SMB_AT 0xd4 `beq a2, a0` (a0 = 4), then SMB_AT 0xdc `bne a2, a0` (a0 = 3) *)
Definition smb_rd1 := smb_prun smb_SH (add_cond smb_ssD (mkAC BC_LTU (SLit 1) (SOff 33 (-5)))).
Definition smb_rd2 := smb_prun smb_SH (smb_pbr smb_rd1 false).
(* the string arm's first hand load, SMB_AT 0x34c `ld a0, 0(a0)` (a0 = a + 16) *)
Definition smb_ssS : sstate := Eval vm_compute in smb_pfin (smb_prun smb_SH (smb_pbr smb_rd1 true)).
(* the number arm's first hand load, SMB_AT 0x108 `ld a0, 0(a0)` (a0 = a + 16) *)
Definition smb_ssN : sstate := Eval vm_compute in smb_pfin (smb_prun smb_SH (smb_pbr smb_rd2 false)).

(* ---- the token runner (YCbqG.v SRr_run_tok_AJx / SRr_run_to_tok_AJx; cgif YCbq.v aj_run_tok with the 16 journal
   binders of ajournal_x), over the listing's whole-range table; before the run it records the run's memnorm keep
   (YGcallMxmn.memnorm_frame_of at the run's start state) as HMNP ---- *)
Ltac smb_run HS HJ SHOK :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let HMNP := fresh "HMNP" in
    pose proof (fun m' Hmn HF => memnorm_frame_of segs (w_H W) E ss ms m' Hmn HS HF) as HMNP;
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_runN_tok segs B_prog_tbl K Bx BAND_SPAN SH YP03.FUEL ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_runN_tok segs B_prog_tbl K Bx BAND_SPAN SH YP03.FUEL ss = (st', rs)) by (vm_compute; reflexivity);
          let HL := lazymatch goal with H : AR_laws_x _ _ _ _ |- _ => H end in
          eapply (SRr_run_tok_AJx segs _ _ _ HL B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx W YP03.FUEL E K Bx
            BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun HS HJ SHOK; aj_after_run_tok HS HJ SHOK ]
        end
    end
  end.
Ltac smb_run_to HS HJ SHOK stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let HMNP := fresh "HMNP" in
    pose proof (fun m' Hmn HF => memnorm_frame_of segs (w_H W) E ss ms m' Hmn HS HF) as HMNP;
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_run_toN_tok segs B_prog_tbl K Bx BAND_SPAN SH YP03.FUEL stop ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_run_toN_tok segs B_prog_tbl K Bx BAND_SPAN SH YP03.FUEL stop ss = (st', rs))
            by (vm_compute; reflexivity);
          let HL := lazymatch goal with H : AR_laws_x _ _ _ _ |- _ => H end in
          eapply (SRr_run_to_tok_AJx segs _ _ _ HL B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx W YP03.FUEL stop E
            K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun HS HJ SHOK; aj_after_run_tok HS HJ SHOK ]
        end
    end
  end.
(* the state stops at a branch it cannot decide: split on it *)
Ltac smb_branch HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_step segs B_prog_tbl ss) in
    lazymatch r with
    | SStop (SR_branch ?c ?a ?b) =>
      apply (SRr_sym_branch segs W E ss ms _ _ c a b HS); clear HS
    | _ => fail "smb_branch: not stopped at a branch:" r
    end
  end.
(* the write windows of a run: the frame (base sp, inside the window STK) and read-only regions *)
Ltac smb_awr Usp FS :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite FS; cbn [YP09.r_wlo]; lia
      | cbn [YP09.r_whi]; lia |] ].
(* every write window of a run lies at or above YM05.alloc_ceiling (goal: forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) *)
Ltac smb_wb Usp Hc :=
  let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
    try rewrite Usp in Hx; lia|]); destruct Hin.
(* a hand load `lw rd, imm(rs)` / `ld rd, imm(rs)` at the state HS: the instruction word and the fresh atom are computed;
   left: the base register's value, the address bounds, the loaded value's val_mem fact and range, the continuation *)
Ltac smb_hl_lw HS rd rs base v :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let o := eval vm_compute in (clookup B_prog_tbl (ss_pc ss)) in
    let K := eval vm_compute in (run_K 0 smb_Bx smb_SH ss) in
    lazymatch o with Some ?w =>
      eapply (smb_hlwv segs B_prog_wx B_prog_tbl B_prog_tbl_ok W E ss ms _ rd rs 0%bv w base v K _ HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv
      | vm_compute; reflexivity | | | | | | | ]
    end end.
Ltac smb_hl_ld HS rd rs imm base v :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let o := eval vm_compute in (clookup B_prog_tbl (ss_pc ss)) in
    let K := eval vm_compute in (run_K 0 smb_Bx smb_SH ss) in
    lazymatch o with Some ?w =>
      eapply (smb_hld8v segs B_prog_wx B_prog_tbl B_prog_tbl_ok W E ss ms _ rd rs imm w base v K _ HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv
      | vm_compute; reflexivity | | | | | | | ]
    end end.
(* the base register's value: its symbolic value is the given sv, whose denotation is the given word *)
Ltac smb_regv v :=
  lazymatch goal with |- sv_denot ?E (sr_get ?r ?x) = _ =>
    transitivity (sv_denot E v); [f_equal; vm_compute; reflexivity|] end.

(* ---- small value lemmas (Wsame.v's, renamed) ---- *)
Lemma smb_ew_new1 : forall E k (v : word), ew (havoc E k [v]) k = v.
Proof.
intros E k v. pose proof (ew_havoc_new E k [v] 0 v ltac:(cbn; lia)) as H. rewrite Nat.add_0_r in H. exact H.
Qed.
Lemma smb_denot_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x H Hx Hxc. apply bv_eq. rewrite denot_SOff, H, !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma smb_U_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  U E (SOff n c) = x + c.
Proof.
intros E n c x H Hx Hxc. unfold U. rewrite (smb_denot_off E n c x H Hx Hxc). apply unsigned_lit_small. lia.
Qed.
(* `seqz s1, a0; mv a0, s1` as the engine leaves it: a0 = 1 exactly when the atom is 0 *)
Lemma smb_U_seqz : forall E k (v : word), ew E k = v ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff k 0) (SLit 1)) (SLit 0)) = if bv_unsigned v =? 0 then 1 else 0.
Proof.
intros E k v Hk. rewrite !U_SAlu, !U_lit by lia.
assert (Ua : U E (SOff k 0) = bv_unsigned v) by (unfold U; rewrite smbk_SOff0, Hk; reflexivity).
rewrite Ua. pose proof (bv_unsigned_in_range _ v) as Hr. unfold zalu_raw.
destruct (Z.eqb_spec (bv_unsigned v) 0) as [H0 | H0].
- rewrite H0. reflexivity.
- replace (bv_unsigned v <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* the address an `add` of two atoms leaves: their sum, without wrap *)
Lemma smb_denot_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)))) with (U E (SAlu ALU_ADD (SOff a 0) (SOff b 0))).
rewrite U_SAlu, (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)). cbn [zalu_raw].
rewrite unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* ---- the values the loop's checks compute (SMB_AT 0x1e8 / 0x208 / 0x234 / 0x254 / 0x2a4 / 0x2bc / 0x2d0) ---- *)
Lemma smb_U_add_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite U_SAlu, (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)).
cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the UBSan alignment check of a key slot: (8 i + keys) & 7 *)
Lemma smb_U_and7 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> (x + y) mod 8 = 0 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SOff a 0) (SOff b 0)) (SLit 7)) = 0.
Proof.
intros E a b x y Ha Hb Hx Hy Hxy H8.
rewrite U_SAlu, (smb_U_add_atoms E a b x y Ha Hb Hx Hy Hxy), U_lit by lia.
cbn [zalu_raw]. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite H8. reflexivity.
Qed.
(* i * 56 (`slli; slli; sub` as the engine leaves it is a mul) *)
Lemma smb_U_mul56 : forall E a x, ew E a = Z_to_bv 64 x -> 0 <= x -> 56 * x < 2 ^ 63 ->
  U E (SMd M_MUL (SOff a 0) (SLit 56)) = 56 * x.
Proof.
intros E a x Ha Hx Hb. rewrite U_SMd, (U_atom E a x Ha ltac:(lia)), U_lit by lia. cbn [zmd_raw].
unfold zcanon, M64. rewrite Z.mod_small by lia. ring.
Qed.
(* the kid address kids + 56 i *)
Lemma smb_U_add_mul56 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> 56 * x + y < 2 ^ 63 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit 56)) (SOff b 0)) = 56 * x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hxy.
rewrite U_SAlu, (smb_U_mul56 E a x Ha Hx ltac:(lia)), (U_atom E b y Hb ltac:(lia)).
cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the UBSan overflow check of i * 56: mulh (i, 56) xor ((i * 56) >>s 63) <> 0 *)
Lemma smb_U_mulh56 : forall E a x, ew E a = Z_to_bv 64 x -> 0 <= x -> 56 * x < 2 ^ 63 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff a 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff a 0) (SLit 56)) (SLit 63)))) = 0.
Proof.
intros E a x Ha Hx Hb.
assert (U1 : U E (SMd M_MULH (SOff a 0) (SLit 56)) = 0).
{ rewrite U_SMd, (U_atom E a x Ha ltac:(lia)), U_lit by lia. cbn [zmd_raw].
  rewrite !swrap64_id by (unfold half64; lia). change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (U2 : U E (SAlu ALU_SRA (SMd M_MUL (SOff a 0) (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu, (smb_U_mul56 E a x Ha Hx Hb), U_lit by lia. cbn [zalu_raw].
  rewrite swrap64_id by (unfold half64; lia). change (Z.land 63 63) with 63.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
rewrite U_SAlu, U_lit by lia. rewrite U_SAlu, U1, U2. reflexivity.
Qed.

Lemma smb_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1. induction l1 as [|[k f] r IH]; intros l2 H1 H2; [exact H2|].
destruct H1 as [Hf Hr]. split; [exact Hf | exact (IH l2 Hr H2)].
Qed.

Section rb. Context {fx : YK11.FPState}.
(* a register re-expressed as a fresh atom holding its value (an address the token runner then knows by name) *)
Lemma smb_rebind : forall E ss (H : word -> bool) ms K (r : bv 5) (v : word),
  st_ok rsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true -> bv_eqb r 0 = false ->
  getr (ms_regs ms) r = v ->
  st_ok rsegs (havoc E K [v]) (set_regs_pc ss [(r, SOff K 0)] (ss_pc ss)) (restrict H ms).
Proof.
intros E ss H ms K r v HS Hrv Hat Hr Hv.
pose proof (st_ok_restrict_mkst rsegs H E ss ms HS Hrv) as Hshape.
rewrite Hshape in HS |- *. rewrite restrict_mkst_fx in HS |- *.
apply (st_ok_set_regs rsegs K E (havoc E K [v]) ss (ms_regs ms) (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ss_pc ss)
  (mrestrict H (ms_mem ms)) [(r, SOff K 0)] HS (env_agree_havoc E K [v]) Hat Hrv).
- reflexivity.
- intros q _. reflexivity.
- constructor; [|constructor]. cbn [fst snd]. split; [exact Hr|].
  rewrite smbk_SOff0. rewrite Hv. symmetry. exact (smb_ew_new1 E K v).
Qed.
End rb.

(* ---- the loop's canonical state: at the loop head SMB_AT 0x1bc and at the kids part SMB_AT 0x278 the registers the
   loop keeps (sp, gp, tp, s0 = a, s1 = 1, s2 = a + 40, s4 / s5 the shadow cells of a + 24 / b + 24, s6 = b + 24, s7 the
   shadow offset, s8 / s9 the shadow cells of a / a + 40) are those of the first arrival; s3 = i (atom 56), s10 = 8 i
   (atom 57) and s11 = 56 i (atom 58) count the items done; the caller-saved registers are atoms 40..55 holding
   whatever they hold. The frame smb_frameL is the first arrival's, computed: the callee-saved registers, 3 at 8(sp)
   (the 4-byte tag check's (a & 7) + 3), the shadow cells of b + 32 / a + 32 at 16(sp) / 32(sp), b + 32 / a + 32 at
   24(sp) / 40(sp), a + 24 at 48(sp). The facts on the counters: i <= 2 ^ 25, 8 i <= 2 ^ 28, 56 i <= 2 ^ 30 (DERIVED:
   56 i < 56 cap <= cf_malloc_max <= 2 ^ 30 - 15, YG08cf.cf_malloc_max_bound) ---- *)
Definition smb_frameL : YP09.region := Eval vm_compute in
  hd smb_got_r (ss_mem (smb_pfin (smb_prun_to smb_SH (SMB_AT 0x1bc) (smb_pbr smb_rC false)))).
Definition smb_rsL : smem := [smb_frameL].
Lemma smb_mem_ok_hd : forall E m r rs, mem_ok rsegs E m (r :: rs) -> mem_ok rsegs E m [r].
Proof.
intros E m r rs (Hwf & Hok & _). cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [Hw _].
split; [cbn [regions_wf]; rewrite Hw; reflexivity|].
split; [inversion Hok; subst; constructor; [assumption | constructor]|].
cbn; tauto.
Qed.
Definition smb_shc (v : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL v (SLit 3)) (SOff 32 0).
Definition smb_srL : list sv :=
  [SLit 0; SOff 40 0; SOff 2 (-160); SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 10 0; SLit 1;
   SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0; SOff 10 40; SOff 56 0;
   smb_shc (SOff 10 24); smb_shc (SOff 11 24); SOff 11 24; SOff 32 0; smb_shc (SOff 10 0); smb_shc (SOff 10 40);
   SOff 57 0; SOff 58 0; SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0].
Definition smb_fsL : facts := mkFacts (f_atoms smb_fs0 ++ [(56%nat, mkAF 0 (2 ^ 25) 0); (57%nat, mkAF 0 (2 ^ 28) 3);
  (58%nat, mkAF 0 (2 ^ 30) 3)]) [] [].
Definition smb_ssL (pc : Z) : sstate := mkSS pc smb_srL smb_rsL None smb_fsL.
Definition smb_EL (Ex0 : env) (regsJ : bvmap 5 word) (i : Z) : env :=
  havoc Ex0 40 (map (getr regsJ) CLOB ++ [Z_to_bv 64 i; Z_to_bv 64 (8 * i); Z_to_bv 64 (56 * i)]).
Definition smb_FIXED : list (bv 5) := [0; 2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25]%bv.
Definition smb_fixed_ok (srs : list sv) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get smb_srL r)) smb_FIXED.

Lemma smb_EL_low : forall Ex0 regsJ i k, (k < 40)%nat -> ew (smb_EL Ex0 regsJ i) k = ew Ex0 k.
Proof. intros Ex0 regsJ i k Hk. unfold smb_EL. apply ew_havoc_old. exact Hk. Qed.
Lemma smb_EL_i : forall Ex0 regsJ i, ew (smb_EL Ex0 regsJ i) 56 = Z_to_bv 64 i.
Proof. intros. unfold smb_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.
Lemma smb_EL_i8 : forall Ex0 regsJ i, ew (smb_EL Ex0 regsJ i) 57 = Z_to_bv 64 (8 * i).
Proof. intros. unfold smb_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.
Lemma smb_EL_i56 : forall Ex0 regsJ i, ew (smb_EL Ex0 regsJ i) 58 = Z_to_bv 64 (56 * i).
Proof. intros. unfold smb_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.

(* one register of the canonical form: a kept register (its value from the current state), a loop counter, or a
   caller-saved register (its own value) *)
Ltac smb_regfixed Hregs Hfix HCL rr v :=
  lazymatch type of Hfix with smb_fixed_ok ?srs = true =>
    rewrite (Hregs rr);
    let Hx := fresh "Hx" in
    assert (Hx : sv_eqb (sr_get srs rr) (sr_get smb_srL rr) = true)
      by (apply (proj1 (forallb_forall _ _) Hfix); unfold smb_FIXED; cbn [In];
          repeat first [ (left; reflexivity) | right ]);
    apply sv_eqb_eq in Hx; rewrite Hx;
    change (sr_get smb_srL rr) with v;
    symmetry; apply (sv_denot_agree 40 _ _ v HCL); vm_compute; reflexivity
  end.
Ltac smb_regcase Hregs Hfix HCL R19 R26 R27 :=
  lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get smb_srL ?rr) =>
    let v := eval vm_compute in (sr_get smb_srL rr) in
    lazymatch v with
    | SOff ?k 0 =>
        let b := eval vm_compute in (Nat.leb 40 k) in
        lazymatch b with
        | true => change (sr_get smb_srL rr) with v; rewrite smbk_SOff0; unfold smb_EL, havoc, CLOB; cbn [ew];
                  first [ reflexivity | exact R19 | exact R26 | exact R27 ]
        | false => smb_regfixed Hregs Hfix HCL rr v
        end
    | _ => smb_regfixed Hregs Hfix HCL rr v
    end
  end.

(* the items of a container, keys first (an array's keys are []) *)
Definition smb_its (t : jv) : list (list Z * jv) :=
  match t with JArr l => map (fun u => ([], u)) l | JObj l => l | _ => [] end.
Lemma smb_its_inj : forall t u, tag t = tag u -> (tag t = 5 \/ tag t = 6) -> smb_its t = smb_its u -> t = u.
Proof.
intros t u Et Hc E.
destruct t as [| | | ? ? | ? | la | ma]; destruct u as [| | | ? ? | ? | lb | mb]; cbn [tag smb_its] in *; try lia.
- f_equal. apply (f_equal (map snd)) in E. rewrite !map_map in E. cbn in E. rewrite !map_id in E. exact E.
- f_equal. exact E.
Qed.
Lemma smb_its_key5 : forall t i nm u, tag t = 5 -> nth_error (smb_its t) i = Some (nm, u) -> nm = [].
Proof.
intros [| | | ? ? | ? | l | l] i nm u Ht E; cbn [tag] in Ht; try lia. cbn [smb_its] in E.
rewrite nth_error_map in E. destruct (nth_error l i); cbn in E; [injection E as E1 _; symmetry; exact E1 | discriminate].
Qed.
Lemma smb_its_depth : forall t i nm u, nth_error (smb_its t) i = Some (nm, u) -> (depth u < depth t)%nat.
Proof.
intros [| | | ? ? | ? | l | l] i nm u E; cbn [smb_its] in E; try (destruct i; discriminate).
- rewrite nth_error_map in E. destruct (nth_error l i) as [v|] eqn:El; cbn in E; [|discriminate].
  injection E as _ E2. subst v. exact (smb_depth_nth l i u El).
- exact (smb_depth_nthm l i nm u E).
Qed.

(* ---- the unwinder's frame chain (YG00.v fpchain, YCbq.v achain) at an address whose words up to the stack top are
   all readable: it exists, built word by word as the unwinder reads (a word below 4096 ends it, bad_next ends it,
   else it goes on at the next frame pointer, strictly higher) ---- *)
Lemma smb_aview_nonneg : forall segs H m a v, aview segs H m a = Some v -> 0 <= v.
Proof.
intros segs H m a v E. unfold aview in E. destruct (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; [|discriminate].
injection E as <-. destruct (bv_unsigned_in_range _ b) as [H0 _]. exact H0.
Qed.
Lemma smb_rdword_some : forall (rd : reader) a,
  (forall k, 0 <= k < 8 -> exists v, rd (a + k) = Some v /\ 0 <= v) -> exists w, rdword rd a = Some w /\ 0 <= w.
Proof.
intros rd a H.
destruct (H 0 ltac:(lia)) as (b0 & E0 & P0). rewrite Z.add_0_r in E0.
destruct (H 1 ltac:(lia)) as (b1 & E1 & P1). destruct (H 2 ltac:(lia)) as (b2 & E2 & P2).
destruct (H 3 ltac:(lia)) as (b3 & E3 & P3). destruct (H 4 ltac:(lia)) as (b4 & E4 & P4).
destruct (H 5 ltac:(lia)) as (b5 & E5 & P5). destruct (H 6 ltac:(lia)) as (b6 & E6 & P6).
destruct (H 7 ltac:(lia)) as (b7 & E7 & P7).
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [reflexivity | lia].
Qed.
Lemma smb_fpchain_ex : forall (rd : reader) top (n : nat) bp,
  (Z.to_nat (top - bp) <= n)%nat -> bp mod 8 = 0 -> bp < top - 16 ->
  (forall a, bp - 16 <= a -> a + 8 <= top -> exists w, rdword rd a = Some w /\ 0 <= w) ->
  exists ch, fpchain (rdword rd) bp top ch.
Proof.
intros rd top n. induction n as [|n IH]; intros bp Hn Hal Hbt Hrd; [lia|].
destruct (Hrd (bp - 8) ltac:(lia) ltac:(lia)) as (r & Hr & Hr0).
destruct (Z_lt_dec r 4096) as [Hlt | Hge].
{ exists []. cbn [fpchain]. exists r. split; [exact Hr | lia]. }
destruct (Hrd (bp - 16) ltac:(lia) ltac:(lia)) as (nfp & Hnfp & _).
destruct (bad_next bp top nfp) eqn:Eb.
{ exists [(bp, r, nfp)]. cbn [fpchain]. rewrite Eb.
  split; [reflexivity|]. split; [exact Hal|]. split; [exact Hr|]. split; [exact Hnfp|]. split; [lia | reflexivity]. }
pose proof Eb as Eb'. unfold bad_next in Eb'. apply orb_false_iff in Eb' as [Eb1 Eb3].
apply orb_false_iff in Eb1 as [Eb1 Eb2].
apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. apply negb_false_iff, Z.eqb_eq in Eb3.
destruct (IH nfp ltac:(lia) Eb3 ltac:(lia) ltac:(intros a Ha1 Ha2; apply Hrd; lia)) as (ch & Hch).
exists ((bp, r, nfp) :: ch). cbn [fpchain]. rewrite Eb.
split; [reflexivity|]. split; [exact Hal|]. split; [exact Hr|]. split; [exact Hnfp|]. split; [lia | exact Hch].
Qed.
Section ch. Context {rc : YM05.RunCeil}.
Lemma smb_achain_ex : forall ly (rd : reader) sp v,
  v mod 8 = 0 ->
  (YM05.alloc_ceiling <= v -> v < ly_top ly - 16 -> sp + 16 <= v /\
     forall a, v - 16 <= a -> a + 8 <= ly_top ly -> exists w, rdword rd a = Some w /\ 0 <= w) ->
  exists ch, achain ly rd sp v ch.
Proof.
intros ly rd sp v Hal H.
destruct (Z_lt_dec v YM05.alloc_ceiling) as [Hlo | Hhi].
{ exists []. left. split; [left; exact Hlo | reflexivity]. }
destruct (Z_le_dec (ly_top ly - 16) v) as [Htop | Htop].
{ exists []. left. split; [right; left; exact Htop | reflexivity]. }
destruct (H ltac:(lia) ltac:(lia)) as [Hsp Hrd].
destruct (smb_fpchain_ex rd (ly_top ly) (Z.to_nat (ly_top ly - v)) v ltac:(lia) Hal ltac:(lia) Hrd) as (ch & Hch).
exists ch. right. split; [exact Hsp|]. split; [lia|]. split; [exact Hal|]. split; [exact Hch|].
eapply Forall_impl; [|exact (fpchain_fps_increase _ _ _ _ Hch)]. intros r Hr. cbn beta in Hr. lia.
Qed.
End ch.

(* 8-alignment facts the loop's checks use *)
Lemma smb_mod8_of16 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
intros a H. apply Z.mod_divide in H as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with (2 * q * 8) by ring.
apply Z_mod_mult.
Qed.
Lemma smb_mod8_add8 : forall x a, a mod 8 = 0 -> (8 * x + a) mod 8 = 0.
Proof. intros x a H. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. exact H. Qed.
