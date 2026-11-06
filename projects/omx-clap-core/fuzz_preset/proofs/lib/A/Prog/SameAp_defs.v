(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the walk of same (fuzz_preset.c:65-86) at image A' (asan #102 pin
   1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4), against the kit's text tsame_specX (lib/A/PRH_FnEx.v :353 at the cut
   7cdbb61b5fa0; SameAp_walk.v's same_holds_Ap), over the whole-program listing
   A_prog_listing / PI_prog_A (lib/A/Listing_prog.v, PAImg_prog.v of the cut): same is A_prog_sigma AS_same, 187
   instructions, frame 128. This file: the image numbers, the entry state, the run tactics, the segment states, the
   loop's canonical state and the value lemmas.
   RELOCATION. The instruction walk is the old-A walk (a Theorem Labs lane's slice S9, lib/A/Prog/Wsame.v at
   a working branch 9a0674f0b5f2, old pin d83eb25d). Old A and A' same are the
   same 748 bytes modulo 19 words: the lo12 of the .got load at word 15 (both load the .got slot of
   __asan_shadow_memory_dynamic_address: here SMA_GOT, the listing's object 0) and 18 jal displacements (to the same
   callees). So every state of the old walk is the A' state with its pc moved: the old walk's entry + o is SMA_AT o
   here (the segment states sma_ssD / sma_ssN / sma_ssS / sma_ssC are at SMA_AT 0xb4 / 0xf0 / 0x24c / 0x144), the .got slot and the
   shadow-base cell are SMA_GOT / SMA_CELL (PALib's A_OBJ 0 / A_OBJ 12), the strcmp / bcmp wrappers SMA_STRCMP /
   SMA_BCMP. The run tactics, the image numbers and the memnorm keep each run records (HMNP, for fpostm) are
   lib/B/Prog/SameB_defs.v's (a working branch e95b6ce78e87) at A_prog_tbl.
   Numerals: SMA_AT offsets are LENGTHs (byte offsets inside the 748-byte body); 128 (LENGTH: the frame), 56 / 40 / 32 /
   24 / 16 / 8 (LENGTH: struct pj and its fields, the frame slots), 3 / 4 / 5 / 6 (WORD: the tags), 2 ^ 46 / 2 ^ 47 /
   4096 (DERIVED: address-space bounds), 0x400 (LENGTH: a bound on the body). No ADDRESS: every image number is an
   A_prog_sigma / A_prog_val term of the listing. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import SameAp_kit SameAp_memA SameAp_memB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* ---- the image numbers, all from the listing ---- *)
(* a pc inside the body of same, by its byte offset from the entry *)
Definition SMA_AT (o : Z) : Z := A_prog_sigma AS_same + o.
Definition SMA_GOT : Z := A_prog_val (A_OBJ 0).
Definition SMA_CELL : Z := A_prog_val (A_OBJ 12).
Definition SMA_STRCMP : Z := A_prog_sigma AS___wrap_strcmp.
Definition SMA_BCMP : Z := A_prog_sigma AS___wrap_bcmp.
Lemma sma_obj_bounds : 4096 <= SMA_GOT /\ SMA_GOT + 8 <= SMA_CELL /\ SMA_CELL + 8 <= 2 ^ 32.
Proof.
unfold SMA_GOT, SMA_CELL.
let g := eval vm_compute in (A_prog_val (A_OBJ 0)) in change (A_prog_val (A_OBJ 0)) with g.
let c := eval vm_compute in (A_prog_val (A_OBJ 12)) in change (A_prog_val (A_OBJ 12)) with c.
lia.
Qed.
Lemma sma_pc_bounds : 4096 <= A_prog_sigma AS_same /\ A_prog_sigma AS_same + 0x400 < 2 ^ 32 /\
  4096 <= SMA_STRCMP < 2 ^ 32 /\ 4096 <= SMA_BCMP < 2 ^ 32.
Proof.
unfold SMA_AT, SMA_STRCMP, SMA_BCMP.
let g := eval vm_compute in (A_prog_sigma AS_same) in change (A_prog_sigma AS_same) with g.
let g := eval vm_compute in (A_prog_sigma AS___wrap_strcmp) in change (A_prog_sigma AS___wrap_strcmp) with g.
let g := eval vm_compute in (A_prog_sigma AS___wrap_bcmp) in change (A_prog_sigma AS___wrap_bcmp) with g.
lia.
Qed.

(* THE NAME GUARD: rsegs here is image A's (lib/A/Img0.v), never the plain image's lib/Img0.v; and the listing
   instance's segments are it *)
Lemma sma_rsegs_is_A : True.
Proof.
lazymatch constr:(rsegs) with OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs => exact I end.
Qed.
Lemma sma_pa_segs_A {rc : YM05.RunCeil} : @pa_segs rc A_prog_listing PI_prog_A = rsegs.
Proof. reflexivity. Qed.

(* ---- the symbolic entry state: the frame, the .got slot of the shadow base and the base cell (atom 32 = the shadow
   offset); the facts on sp (atom 2), pa (atom 10), pb (atom 11) and the shadow offset ---- *)
Definition sma_got_r : YP09.region :=
  YP09.mkRegion None SMA_GOT (SMA_GOT + 8) 0 0 [YP09.mkChunk SMA_GOT (CVal 8 (SLit SMA_CELL))].
Definition sma_cell_r : YP09.region :=
  YP09.mkRegion None SMA_CELL (SMA_CELL + 8) 0 0 [YP09.mkChunk SMA_CELL (CVal 8 (SOff 32 0))].
Definition sma_fs0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 56) 3);
  (11%nat, mkAF 4096 (2 ^ 47 - 56) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition sma_ss0 : sstate := mkSS (SMA_AT 0) sr_atoms [smak_fstk 128; sma_got_r; sma_cell_r] None sma_fs0.
Definition sma_SH : list shent := [mkSHE 10 0 56; mkSHE 11 0 56].
Definition sma_Bx : sv := SOff 32 0.
(* ---- the token runner (YCbqG.v SRr_run_tok_AJx / SRr_run_to_tok_AJx; cgif YCbq.v aj_run_tok with the 16 journal
   binders of ajournal_x), over the listing's whole-range table; before the run it records the run's memnorm keep
   (YGcallMxmn.memnorm_frame_of at the run's start state) as HMNP ---- *)
Ltac sma_run HS HJ SHOK :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let HMNP := fresh "HMNP" in
    pose proof (fun m' Hmn HF => memnorm_frame_of segs (w_H W) E ss ms m' Hmn HS HF) as HMNP;
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_runN_tok segs A_prog_tbl K Bx BAND_SPAN SH YP03.FUEL ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_runN_tok segs A_prog_tbl K Bx BAND_SPAN SH YP03.FUEL ss = (st', rs)) by (vm_compute; reflexivity);
          let HL := lazymatch goal with H : AR_laws_x _ _ _ _ |- _ => H end in
          eapply (SRr_run_tok_AJx segs _ _ _ HL A_prog_segs_low A_prog_tbl A_prog_tbl_ok A_prog_wx W YP03.FUEL E K Bx
            BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun HS HJ SHOK; aj_after_run_tok HS HJ SHOK ]
        end
    end
  end.
Ltac sma_run_to HS HJ SHOK stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let HMNP := fresh "HMNP" in
    pose proof (fun m' Hmn HF => memnorm_frame_of segs (w_H W) E ss ms m' Hmn HS HF) as HMNP;
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_run_toN_tok segs A_prog_tbl K Bx BAND_SPAN SH YP03.FUEL stop ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_run_toN_tok segs A_prog_tbl K Bx BAND_SPAN SH YP03.FUEL stop ss = (st', rs))
            by (vm_compute; reflexivity);
          let HL := lazymatch goal with H : AR_laws_x _ _ _ _ |- _ => H end in
          eapply (SRr_run_to_tok_AJx segs _ _ _ HL A_prog_segs_low A_prog_tbl A_prog_tbl_ok A_prog_wx W YP03.FUEL stop E
            K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun HS HJ SHOK; aj_after_run_tok HS HJ SHOK ]
        end
    end
  end.
(* the state stops at a branch it cannot decide: split on it *)
Ltac sma_branch HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_step segs A_prog_tbl ss) in
    lazymatch r with
    | SStop (SR_branch ?c ?a ?b) =>
      apply (SRr_sym_branch segs W E ss ms _ _ c a b HS); clear HS
    | _ => fail "sma_branch: not stopped at a branch:" r
    end
  end.
(* the write windows of a run: the frame (base sp, inside the window STK) and read-only regions *)
Ltac sma_awr Usp FS :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite FS; cbn [YP09.r_wlo]; lia
      | cbn [YP09.r_whi]; lia |] ].
(* every write window of a run lies at or above YM05.alloc_ceiling (goal: forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) *)
Ltac sma_wb Usp Hc :=
  let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
    try rewrite Usp in Hx; lia|]); destruct Hin.
(* a hand load `lw rd, imm(rs)` / `ld rd, imm(rs)` at the state HS: the instruction word and the fresh atom are computed;
   left: the base register's value, the address bounds, the loaded value's val_mem fact and range, the continuation *)
Ltac sma_hl_lw HS rd rs base v :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let o := eval vm_compute in (clookup A_prog_tbl (ss_pc ss)) in
    let K := eval vm_compute in (run_K 0 sma_Bx sma_SH ss) in
    lazymatch o with Some ?w =>
      eapply (sma_hlwv segs A_prog_wx A_prog_tbl A_prog_tbl_ok W E ss ms _ rd rs 0%bv w base v K _ HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv
      | vm_compute; reflexivity | | | | | | | ]
    end end.
Ltac sma_hl_ld HS rd rs imm base v :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let o := eval vm_compute in (clookup A_prog_tbl (ss_pc ss)) in
    let K := eval vm_compute in (run_K 0 sma_Bx sma_SH ss) in
    lazymatch o with Some ?w =>
      eapply (sma_hld8v segs A_prog_wx A_prog_tbl A_prog_tbl_ok W E ss ms _ rd rs imm w base v K _ HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv
      | vm_compute; reflexivity | | | | | | | ]
    end end.
(* the base register's value: its symbolic value is the given sv, whose denotation is the given word *)
Ltac sma_regv v :=
  lazymatch goal with |- sv_denot ?E (sr_get ?r ?x) = _ =>
    transitivity (sv_denot E v); [f_equal; vm_compute; reflexivity|] end.
(* ---- small value lemmas (Wsame.v's, renamed) ---- *)
Lemma sma_ew_new1 : forall E k (v : word), ew (havoc E k [v]) k = v.
Proof.
intros E k v. pose proof (ew_havoc_new E k [v] 0 v ltac:(cbn; lia)) as H. rewrite Nat.add_0_r in H. exact H.
Qed.
Lemma sma_denot_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x H Hx Hxc. apply bv_eq. rewrite denot_SOff, H, !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma sma_U_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  U E (SOff n c) = x + c.
Proof.
intros E n c x H Hx Hxc. unfold U. rewrite (sma_denot_off E n c x H Hx Hxc). apply unsigned_lit_small. lia.
Qed.
(* `seqz s0, a0; mv a0, s0` as the engine leaves it: a0 = 1 exactly when the atom is 0 *)
Lemma sma_U_seqz : forall E k (v : word), ew E k = v ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff k 0) (SLit 1)) (SLit 0)) = if bv_unsigned v =? 0 then 1 else 0.
Proof.
intros E k v Hk. rewrite !U_SAlu, !U_lit by lia.
assert (Ua : U E (SOff k 0) = bv_unsigned v) by (unfold U; rewrite smak_SOff0, Hk; reflexivity).
rewrite Ua. pose proof (bv_unsigned_in_range _ v) as Hr. unfold zalu_raw.
destruct (Z.eqb_spec (bv_unsigned v) 0) as [H0 | H0].
- rewrite H0. reflexivity.
- replace (bv_unsigned v <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* the address an `add` of two atoms leaves: their sum, without wrap *)
Lemma sma_denot_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)))) with (U E (SAlu ALU_ADD (SOff a 0) (SOff b 0))).
rewrite U_SAlu, (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)). cbn [zalu_raw].
rewrite unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Section rb. Context {fx : YK11.FPState}.
(* a register re-expressed as a fresh atom holding its value (an address the token runner then knows by name) *)
Lemma sma_rebind : forall E ss (H : word -> bool) ms K (r : bv 5) (v : word),
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
  rewrite smak_SOff0. rewrite Hv. symmetry. exact (sma_ew_new1 E K v).
Qed.
End rb.
(* ---- the segment states (the old walk's, pc moved to SMA_AT; Wsame.v :629-654, :932-941, :1881-1890) ---- *)
Definition sma_frame : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the dispatch point SMA_AT 0xb4 (`bgeu s0, a0`): tags equal, n fields equal; atoms 33 / 34 the tags, 35 / 36 the n fields *)
Definition sma_ssD : sstate := mkSS (SMA_AT 0xb4)
  [SLit 0; SOff 1 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SLit 1; SOff 11 0;
   SOff 33 (-5); SOff 11 40; SLit 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 10 0; SOff 19 0;
   SOff 20 0; SOff 32 0; SOff 33 0; SOff 35 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
   SOff 30 0; SOff 31 0]
  [sma_frame; sma_got_r; sma_cell_r] None
  (mkFacts (f_atoms sma_fs0) [mkAC BC_EQ (SOff 35 0) (SOff 36 0); mkAC BC_EQ (SOff 33 0) (SOff 34 0)] []).
(* the number arm's entry SMA_AT 0xf0 (`ld a0, 0(a0)`, a0 = a + 16, a1 = b + 16): the tag is 3 *)
Definition sma_ssN : sstate := mkSS (SMA_AT 0xf0)
  [SLit 0; SOff 1 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SLit 1; SOff 11 0;
   SOff 10 16; SOff 11 16; SLit 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 10 0; SOff 19 0;
   SOff 20 0; SOff 32 0; SOff 33 0; SOff 35 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
   SOff 30 0; SOff 31 0]
  [sma_frame; sma_got_r; sma_cell_r] None
  (mkFacts (f_atoms sma_fs0) [mkAC BC_EQ (SOff 33 0) (SLit 3); mkAC BC_NE (SOff 33 0) (SLit 4);
    mkAC BC_LTU (SLit 1) (SOff 33 (-5)); mkAC BC_EQ (SOff 35 0) (SOff 36 0); mkAC BC_EQ (SOff 33 0) (SOff 34 0)] []).
(* the string arm's hand loads SMA_AT 0x24c (`ld a0, 0(a0)`, a0 = a + 16, s1 = b + 16, after both shadow checks): tag 4 *)
Definition sma_ssS : sstate := mkSS (SMA_AT 0x24c)
  [SLit 0; SOff 1 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SLit 1; SOff 11 16;
   SOff 10 16; SLit 0; SLit 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 10 0; SOff 19 0;
   SOff 20 0; SOff 32 0; SOff 33 0; SOff 35 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
   SOff 30 0; SOff 31 0]
  [sma_frame; sma_got_r; sma_cell_r] None
  (mkFacts (f_atoms sma_fs0) [mkAC BC_EQ (SOff 33 0) (SLit 4); mkAC BC_LTU (SLit 1) (SOff 33 (-5));
    mkAC BC_EQ (SOff 35 0) (SOff 36 0); mkAC BC_EQ (SOff 33 0) (SOff 34 0)] []).

(* the container arm's entry SMA_AT 0x144 (`beqz s7`, s7 = n): tag 5 or 6 *)
Definition sma_ssC : sstate := mkSS (SMA_AT 0x144)
  [SLit 0; SOff 1 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SLit 1; SOff 11 0;
   SOff 33 (-5); SOff 11 40; SLit 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 10 0; SOff 19 0;
   SOff 20 0; SOff 32 0; SOff 33 0; SOff 35 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
   SOff 30 0; SOff 31 0]
  [sma_frame; sma_got_r; sma_cell_r] None
  (mkFacts (f_atoms sma_fs0) [mkAC BC_GEU (SLit 1) (SOff 33 (-5)); mkAC BC_EQ (SOff 35 0) (SOff 36 0);
    mkAC BC_EQ (SOff 33 0) (SOff 34 0)] []).

(* the n field a node holds: the item count of a container, 0 otherwise *)
Definition sma_len (t : jv) : Z :=
  match t with JArr l => Z.of_nat (length l) | JObj l => Z.of_nat (length l) | _ => 0 end.
(* ---- the loop's canonical state: at the loop head SMA_AT 0x188 and at the kids part SMA_AT 0x1e8 the registers the loop keeps
   (sp, gp, tp, s0 = 1, s1 = b + 24, s2 = a + 24, s3 / s4 / s10 / s11 the shadow cells of a + 24 / b + 24 / b + 32 /
   a + 32, s5 the shadow offset, s6 the tag) are those of the first arrival; s7 = r (atom 56), s8 = 8 i (57), s9 = 56 i
   (58) count the items left and done; the caller-saved registers are atoms 40..55 holding whatever they hold. The
   frame keeps the callee-saved registers and a + 32 / b + 32 at 16(sp) / 8(sp). ---- *)
Definition sma_frameL : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0
  [YP09.mkChunk (-120) (CVal 8 (SOff 11 32)); YP09.mkChunk (-112) (CVal 8 (SOff 10 32));
   YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the loop no longer reads the .got slot or the shadow-base cell: its regions are the frame only *)
Definition sma_rsL : smem := [sma_frameL].
Lemma sma_mem_ok_hd : forall E m r rs, mem_ok rsegs E m (r :: rs) -> mem_ok rsegs E m [r].
Proof.
intros E m r rs (Hwf & Hok & _). cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [Hw _].
split; [cbn [regions_wf]; rewrite Hw; reflexivity|].
split; [inversion Hok; subst; constructor; [assumption | constructor]|].
cbn; tauto.
Qed.
Definition sma_shc (v : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL v (SLit 3)) (SOff 32 0).
Definition sma_srL : list sv :=
  [SLit 0; SOff 40 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0; SLit 1; SOff 11 24;
   SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0; SOff 10 24;
   sma_shc (SOff 10 24); sma_shc (SOff 11 24); SOff 32 0; SOff 33 0; SOff 56 0; SOff 57 0; SOff 58 0;
   sma_shc (SOff 11 32); sma_shc (SOff 10 32); SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0].
Definition sma_ssL (pc : Z) : sstate := mkSS pc sma_srL sma_rsL None sma_fs0.
Definition sma_EL (Ex0 : env) (regsJ : bvmap 5 word) (r i : Z) : env :=
  havoc Ex0 40 (map (getr regsJ) CLOB ++ [Z_to_bv 64 r; Z_to_bv 64 (8 * i); Z_to_bv 64 (56 * i)]).
Definition sma_FIXED : list (bv 5) := [0; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv.
Definition sma_fixed_ok (srs : list sv) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get sma_srL r)) sma_FIXED.

Lemma sma_EL_low : forall Ex0 regsJ r i k, (k < 40)%nat -> ew (sma_EL Ex0 regsJ r i) k = ew Ex0 k.
Proof. intros Ex0 regsJ r i k Hk. unfold sma_EL. apply ew_havoc_old. exact Hk. Qed.
Lemma sma_EL_r : forall Ex0 regsJ r i, ew (sma_EL Ex0 regsJ r i) 56 = Z_to_bv 64 r.
Proof. intros. unfold sma_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.
Lemma sma_EL_i8 : forall Ex0 regsJ r i, ew (sma_EL Ex0 regsJ r i) 57 = Z_to_bv 64 (8 * i).
Proof. intros. unfold sma_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.
Lemma sma_EL_i56 : forall Ex0 regsJ r i, ew (sma_EL Ex0 regsJ r i) 58 = Z_to_bv 64 (56 * i).
Proof. intros. unfold sma_EL, havoc, CLOB. cbn [ew]. reflexivity. Qed.
(* one register of the canonical form: a kept register (its value from the current state), a loop counter, or a
   caller-saved register (its own value) *)
Ltac sma_regfixed Hregs Hfix HCL rr v :=
  lazymatch type of Hfix with sma_fixed_ok ?srs = true =>
    rewrite (Hregs rr);
    let Hx := fresh "Hx" in
    assert (Hx : sv_eqb (sr_get srs rr) (sr_get sma_srL rr) = true)
      by (apply (proj1 (forallb_forall _ _) Hfix); unfold sma_FIXED; cbn [In];
          repeat first [ (left; reflexivity) | right ]);
    apply sv_eqb_eq in Hx; rewrite Hx;
    change (sr_get sma_srL rr) with v;
    symmetry; apply (sv_denot_agree 40 _ _ v HCL); vm_compute; reflexivity
  end.
Ltac sma_regcase Hregs Hfix HCL R23 R24 R25 :=
  lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get sma_srL ?rr) =>
    let v := eval vm_compute in (sr_get sma_srL rr) in
    lazymatch v with
    | SOff ?k 0 =>
        let b := eval vm_compute in (Nat.leb 40 k) in
        lazymatch b with
        | true => change (sr_get sma_srL rr) with v; rewrite smak_SOff0; unfold sma_EL, havoc, CLOB; cbn [ew];
                  first [ reflexivity | exact R23 | exact R24 | exact R25 ]
        | false => sma_regfixed Hregs Hfix HCL rr v
        end
    | _ => sma_regfixed Hregs Hfix HCL rr v
    end
  end.
(* the items of a container, keys first (an array's keys are []) *)
Definition sma_its (t : jv) : list (list Z * jv) :=
  match t with JArr l => map (fun u => ([], u)) l | JObj l => l | _ => [] end.
Lemma sma_its_len : forall t, (tag t = 5 \/ tag t = 6) -> Z.of_nat (length (sma_its t)) = sma_len t.
Proof. intros [| | | ? ? | ? | l | l] H; cbn [tag] in H; try lia; cbn [sma_its sma_len]; [rewrite length_map|]; reflexivity. Qed.
Lemma sma_its_inj : forall t u, tag t = tag u -> (tag t = 5 \/ tag t = 6) -> sma_its t = sma_its u -> t = u.
Proof.
intros t u Et Hc E.
destruct t as [| | | ? ? | ? | la | ma]; destruct u as [| | | ? ? | ? | lb | mb]; cbn [tag sma_its] in *; try lia.
- f_equal. apply (f_equal (map snd)) in E. rewrite !map_map in E. cbn in E. rewrite !map_id in E. exact E.
- f_equal. exact E.
Qed.

Lemma sma_its_key5 : forall t i nm u, tag t = 5 -> nth_error (sma_its t) i = Some (nm, u) -> nm = [].
Proof.
intros [| | | ? ? | ? | l | l] i nm u Ht E; cbn [tag] in Ht; try lia. cbn [sma_its] in E.
rewrite nth_error_map in E. destruct (nth_error l i); cbn in E; [injection E as E1 _; symmetry; exact E1 | discriminate].
Qed.
Lemma sma_its_depth : forall t i nm u, nth_error (sma_its t) i = Some (nm, u) -> (depth u < depth t)%nat.
Proof.
intros [| | | ? ? | ? | l | l] i nm u E; cbn [sma_its] in E; try (destruct i; discriminate).
- rewrite nth_error_map in E. destruct (nth_error l i) as [v|] eqn:El; cbn in E; [|discriminate].
  injection E as _ E2. subst v. exact (sma_depth_nth l i u El).
- exact (sma_depth_nthm l i nm u E).
Qed.
(* ---- the unwinder's frame chain (YG00.v fpchain, YCbq.v achain) at an address whose words up to the stack top are
   all readable: it exists, built word by word as the unwinder reads (a word below 4096 ends it, bad_next ends it,
   else it goes on at the next frame pointer, strictly higher) ---- *)
Lemma sma_aview_nonneg : forall segs H m a v, aview segs H m a = Some v -> 0 <= v.
Proof.
intros segs H m a v E. unfold aview in E. destruct (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; [|discriminate].
injection E as <-. destruct (bv_unsigned_in_range _ b) as [H0 _]. exact H0.
Qed.
Lemma sma_rdword_some : forall (rd : reader) a,
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
Lemma sma_fpchain_ex : forall (rd : reader) top (n : nat) bp,
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
Lemma sma_achain_ex : forall ly (rd : reader) sp v,
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
destruct (sma_fpchain_ex rd (ly_top ly) (Z.to_nat (ly_top ly - v)) v ltac:(lia) Hal ltac:(lia) Hrd) as (ch & Hch).
exists ch. right. split; [exact Hsp|]. split; [lia|]. split; [exact Hal|]. split; [exact Hch|].
eapply Forall_impl; [|exact (fpchain_fps_increase _ _ _ _ Hch)]. intros r Hr. cbn beta in Hr. lia.
Qed.
End ch.

(* 8-alignment facts the loop's checks use *)
Lemma sma_mod8_of16 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
intros a H. apply Z.mod_divide in H as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with (2 * q * 8) by ring.
apply Z_mod_mult.
Qed.
Lemma sma_mod8_add8 : forall x a, a mod 8 = 0 -> (8 * x + a) mod 8 = 0.
Proof. intros x a H. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. exact H. Qed.
