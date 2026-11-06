(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v, with its module paths and module names changed; 1922 of its 1971 lines of code are new or changed and 78 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at a58a6fc257b (parts 1, 2) and
   a6c23b42ca2 (part 3); ported to
   reac-pw/fuzz_headamp image A: module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec -> HPgBase / HPgCSpec, the
   rl_ prefix -> hd_; every image address relocated from role's image A to headamp's (the jump table 0x20e94 ->
   0x20e9c with its nine entries and targets measured from headamp's pinned bytes, the dispatch block 0x80b1c ->
   0x8183c, the two fuzz_u32 sites 0x80ee4 / 0x81454 -> 0x81c04 / 0x82174 and their ends 0x815e8 / 0x8163c ->
   0x82308 / 0x8235c, the code tables over 0x81c04 .. 0x82360 and 0x825bc .. 0x82838); the input-length cell of the
   two fuzz_u32 sites [s1+0xf8] -> [s1+0x118] (headamp's frame-slot map); img_wx, img_segs_low and same_io_wvb are
   stated here (role took them from its cfg walk file, which headamp has no twin of); part 3 (the scope-store
   sites) restated at headamp's fourteen sites, each measured on image A: role's ten builder sites relocated, role's
   role-object pair replaced by headamp's res and x sites, the run 0x82578 stated with the value it leaves in a1
   (hd_scope_stmtAx, hd_inc_a1, sv_addiw1), role's unused fsh_ss2 dropped, fsh_pts added for the 17-granule x
   sites. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgSteps.v, with its module paths and module names changed; 284 of its 348 lines of code are new or changed and 1907 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the straight-line blocks between the last four calls of segment M03 of the walk of
   LLVMFuzzerTestOneInput (0x80c40), each as a block lemma over a machine state in the shape of
   lib/AU/HPgSteps.v hdu_blk_postE (the journal extended, the registers outside clob kept, the frames, blocks, I/O
   state and meter as at the start, every byte outside the write set kept, and what the block computes). Proves no
   function (kind: segment lemma).

   THE CODE (20 words 0x83850 .. 0x8389c; the end pcs are the four callees' entries and 0x838a0)
     RC   0x83850 ld s2,0x138(s1)       x (= F + 0x2c0, the real-frame cell R+0x138)
          0x83854 lw a3,0x7c(s2)        x->n (no instrumented check: the compiler proved the access in bounds)
          0x83858 ld s5,0x48(s1)        F (the real-frame cell R+0x48)
     RCM  0x8385c sw a3,0(s2)           x->rc := a3 (no instrumented check)
          0x83860 .. 0x8386c mv a0,s9; mv a1,s10; mv a2,s2; jal check_object 0x840c0
          0x83870 .. 0x8387c mv a0,s6; mv a1,s9; mv a2,s2; jal check_cells 0x841c0
          0x83880 bltz s9,0x8389c
          0x83884 .. 0x8388c mv a0,s10; mv a1,s2; jal check_keys 0x843a4
          0x83890 .. 0x83898 mv a0,s10; mv a1,s2; jal check_refusal 0x84438
          0x8389c addi a0,zero,-8        then x's 17 shadow bytes := 0xf8 (HPgSteps.hdu_scope_x_out 0x838a0 .. 0x838e4)
   HOW. Each block is one run of the engine (lib/Reusable YCbq aj_run / aj_run_to over br_tbl) from an entry state
   whose registers are atoms; br_blk_rc has three read-only regions (the real-frame cells R+0x48 and R+0x138 with
   two extra atoms for F and x, and x's word x->n with an extra atom for n), br_blk_rcm one writable region (x's
   first word, based at s2; its bytes lie in the frame for locals the harness holds, so the journal may write them:
   YCbq awr_byte's in_frames case), the others none. The branch at 0x83880 is split by srr_branch_with. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the code table ======================================= *)
Definition BR_RC : Z := 0x83850.
Definition BR_RCM : Z := 0x8385c.
Definition BR_OBJ_RET : Z := 0x83870.
Definition BR_CELLS_RET : Z := 0x83880.
Definition BR_KEYS_RET : Z := 0x83890.
Definition BR_REF_RET : Z := 0x8389c.
Definition BR_XOUT : Z := 0x838a0.
Definition BR_CK_OBJECT : Z := 0x840c0.
Definition BR_CK_CELLS : Z := 0x841c0.
Definition BR_CK_KEYS : Z := 0x843a4.
Definition BR_CK_REFUSAL : Z := 0x84438.
Definition br_tbl : ctable := build_table rsegs BR_RC 20 TEmpty.
Lemma br_tbl_ok : table_ok rsegs br_tbl.
Proof. apply build_table_ok0. unfold BR_RC. lia. Qed.

(* ======================================= values ======================================= *)
Lemma br_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
exact (ew_Ereg_nat regs extra n r Hn).
Qed.

Lemma br_atomE : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

(* `bltz` on a small value *)
Lemma br_lt0 : forall rcv, - 2 ^ 31 <= rcv < 2 ^ 31 -> branch_taken BC_LT (Z_to_bv 64 rcv) (Z_to_bv 64 0) = (rcv <? 0).
Proof.
intros rcv Hr. cbn [branch_taken]. unfold bv_lts, bv_signed, bv_swrap. rewrite !Z_to_bv_unsigned.
change (bv_half_modulus 64) with (2 ^ 63). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_mod_idemp_l by lia. rewrite (Z.mod_small (rcv + 2 ^ 63)) by lia.
rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small (0 + 2 ^ 63)) by lia.
replace (rcv + 2 ^ 63 - 2 ^ 63) with rcv by lia. replace (0 + 2 ^ 63 - 2 ^ 63) with 0 by lia. reflexivity.
Qed.

(* the 32-bit load of a word below 2^31 *)
Lemma br_sext32 : forall E (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U. f_equal.
rewrite U_SExt, (U_atom E n v H ltac:(lia)). cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.

(* a stored n-byte chunk read back as the low n bytes of the stored word *)
Section v. Context {fx : YK11.FPState}.
Lemma br_val_of_chunk_w : forall E m base off (n : N) (e : sv),
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem rsegs m (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E m base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. injection Hb1 as <-.
rewrite Hb2. f_equal. unfold YP09.byte_of_word.
assert (Hp : 0 < 2 ^ (8 * Z.of_N n)) by (apply Z.pow_pos_nonneg; lia).
rewrite le_byte_small; [| rewrite Hnn; apply Z.mod_pos_bound; exact Hp | lia].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
symmetry. apply HPgSiteA.hd_shr_mod; lia.
Qed.
End v.

(* ======================================= the blocks ======================================= *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Ltac br_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.

(* the post of a block that writes nothing (its regions, if any, are read-only) *)
Ltac br_post_ro_body HS HJ HFr regs0 clob :=
  red;
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ => exists lyc, Sc end;
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) => exists (ms_regs ms), (ms_mem ms) end; eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs _ _ _ _ HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ _ regs0 _ _ clob HS); [apply env_agree_refl | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [apply Permutation_refl|]; split; [br_io|];
  split; [apply mo_le_refl; assumption|];
  split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
          intros a Ha Hn; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
          let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros (rg & Hin & Hr); vm_compute in Hin;
          repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin|].
Ltac br_post_ro HS HJ HFr regs0 clob := apply SRr_ret; br_post_ro_body HS HJ HFr regs0 clob.

(* RC 0x83850 .. 0x8385c: s2 := x from R+0x138, a3 := x->n, s5 := F from R+0x48 *)
Definition br_rc_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x48 0x50 0 0 [YP09.mkChunk 0x48 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0 [YP09.mkChunk 0x138 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 33%nat) 0x7c 0x80 0 0 [YP09.mkChunk 0x7c (CVal 4 (SOff 34 0))]].
Definition br_ss_rc : sstate := mkSS BR_RC sr_atoms br_rc_regions None (mkFacts [] [] []).

Lemma br_blk_rc : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) R F x n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R -> 0 <= R -> R + 0x140 <= 2 ^ 64 -> 0 <= x -> x + 0x80 <= R + 0x48 ->
0 <= F < 2 ^ 64 -> 0 <= n < 2 ^ 31 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x48) 8 F ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 0x7c) 4 n ->
SRr rsegs W (cfg_at rsegs BR_RC regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_RCM [13; 18; 21]%bv
   (fun _ => False)
   (fun W2 regs2 mem2 => getr regs2 18 = w64 x /\ getr regs2 13 = w64 n /\ getr regs2 21 = w64 F)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R F x n HJ H9 HR0 HR1 Hx0 Hx1 HF Hn VF Vx Vn.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (E := Ereg regs [w64 F; w64 x; w64 n]).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 x) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs E br_ss_rc (restrict (w_H W) (mkst regs (Z_to_bv 64 BR_RC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); change (Ereg regs [w64 F; w64 x; w64 n]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold br_rc_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0x48 8 (SOff 32 0) F); [rewrite denot_lit_U, (U_atom E 32 F E32) by lia; reflexivity
        | cbn; lia | cbn; lia | exact VF].
    + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 33 0) x); [rewrite denot_lit_U, (U_atom E 33 x E33) by lia; reflexivity
        | cbn; lia | cbn; lia | exact Vx].
    + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ x 0x7c 4 (SOff 34 0) n); [rewrite denot_lit_U, (U_atom E 34 n E34) by lia; reflexivity
        | cbn; lia | cbn; lia | exact Vn].
  - unfold br_rc_regions. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, !unsigned_lit_small by lia.
    split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 BR_RC) with (Z_to_bv 64 BR_RC).
aj_run_to br_tbl_ok HS HJ BR_RCM; [awr_ok_tac|].
br_post_ro HS HJ HFr regs ([13; 18; 21]%bv : list (bv 5)).
rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ /\ _ =>
  let e1 := eval vm_compute in (sr_get (ss_regs ss) 18%bv) in change (sr_get (ss_regs ss) 18%bv) with e1;
  let e2 := eval vm_compute in (sr_get (ss_regs ss) 13%bv) in change (sr_get (ss_regs ss) 13%bv) with e2;
  let e3 := eval vm_compute in (sr_get (ss_regs ss) 21%bv) in change (sr_get (ss_regs ss) 21%bv) with e3 end.
split; [exact (br_atomE E 33 x E33)|].
split; [exact (br_sext32 E 34 n E34 Hn)|].
exact (br_atomE E 32 F E32).
Qed.

(* RCM 0x8385c .. 0x840c0: x->rc := a3, then a0 := rc (s9), a1 := res (s10), a2 := x (s2), jal check_object *)
Definition br_xreg : YP09.region := YP09.mkRegion (Some 18%nat) 0 4 0 4 [].
Definition br_ss_rcm : sstate := mkSS BR_RCM sr_atoms [br_xreg] None (mkFacts [] [] []).

Lemma br_blk_rcm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) pos x,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (4, pos) own -> frame_addr lyc 4 pos <= x -> x + 4 <= frame_addr lyc 4 pos + 1024 -> 0 <= x ->
getr regs 18 = w64 x ->
SRr rsegs W (cfg_at rsegs BR_RCM regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_CK_OBJECT [1; 10; 11; 12]%bv
   (fun a => x <= a < x + 4)
   (fun W2 regs2 mem2 => getr regs2 1 = w64 BR_OBJ_RET /\ getr regs2 10 = getr regs 25 /\
      getr regs2 11 = getr regs 26 /\ getr regs2 12 = getr regs 18 /\
      val_mem rsegs (mrestrict (w_H W2) mem2) x 4 (bv_unsigned (getr regs 13) mod 2 ^ 32))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs pos x HJ Hown HxF0 HxF1 Hx0 H18.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (_ & _ & HFb & _).
change (fs_frame_bytes 4) with 1024 in HFb.
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hfin) as (_ & Hceil). cbn [fst snd] in Hceil.
change (fs_frame_bytes 4) with 1024 in Hceil.
pose proof (@alloc_ceiling_lt rc) as Hc47.
assert (E18 : ew (Ereg regs []) 18 = Z_to_bv 64 x) by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (HS : st_ok rsegs (Ereg regs []) br_ss_rcm (restrict (w_H W) (mkst regs (Z_to_bv 64 BR_RCM) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold br_xreg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E18, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFb (x + o) ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 BR_RCM) with (Z_to_bv 64 BR_RCM).
aj_run br_tbl_ok HS HJ;
[ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat x);
  [ reflexivity | rewrite E18; apply unsigned_lit_small; lia
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi br_xreg] in Ha; right; right; right;
    exists 4, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 4) with 1024; lia]
  | apply awr_ok_nil ]
| ].
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) [1; 10; 11; 12]%bv HS);
        [apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [apply Permutation_refl|]. split; [br_io|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val br_xreg] in Hr.
  rewrite E18 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
  lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ /\ _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) 1%bv) in change (sr_get (ss_regs ss) 1%bv) with e1;
    let e2 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e2;
    let e3 := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e3;
    let e4 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in change (sr_get (ss_regs ss) 12%bv) with e4 end.
  split; [reflexivity|].
  split; [apply br_atom; reflexivity|].
  split; [apply br_atom; reflexivity|].
  split; [apply br_atom; reflexivity|].
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E18, unsigned_lit_small in Hch by lia.
  apply Forall_inv in Hch.
  pose proof (br_val_of_chunk_w _ _ _ _ _ _ Hch ltac:(cbn; lia)) as HV.
  rewrite Z.add_0_r in HV. cbn [N.to_nat Pos.to_nat Z.of_N] in HV.
  rewrite (br_atom regs [] 13 13%bv eq_refl) in HV. exact HV.
Qed.

(* the entry state with no region: every register an atom *)
Definition br_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma br_ss0_ok : forall (W : world rsegs) regs memc pc,
st_ok rsegs (Ereg regs []) (br_ss0 pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros W regs memc pc. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* 0x83870 .. 0x841c0: a0 := out (s6), a1 := rc (s9), a2 := x (s2), jal check_cells *)
Lemma br_blk_obj_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
SRr rsegs W (cfg_at rsegs BR_OBJ_RET regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_CK_CELLS [1; 10; 11; 12]%bv
   (fun _ => False)
   (fun W2 regs2 mem2 => getr regs2 1 = w64 BR_CELLS_RET /\ getr regs2 10 = getr regs 22 /\
      getr regs2 11 = getr regs 25 /\ getr regs2 12 = getr regs 18)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs HJ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (br_ss0_ok W regs memc BR_OBJ_RET) as HS.
unfold cfg_at. change (w64 BR_OBJ_RET) with (Z_to_bv 64 BR_OBJ_RET).
aj_run br_tbl_ok HS HJ; [awr_ok_tac|].
br_post_ro HS HJ HFr regs ([1; 10; 11; 12]%bv : list (bv 5)).
rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ /\ _ =>
  let e1 := eval vm_compute in (sr_get (ss_regs ss) 1%bv) in change (sr_get (ss_regs ss) 1%bv) with e1;
  let e2 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e2;
  let e3 := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e3;
  let e4 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in change (sr_get (ss_regs ss) 12%bv) with e4 end.
split; [reflexivity|].
split; [apply br_atom; reflexivity|]. split; [apply br_atom; reflexivity|]. apply br_atom; reflexivity.
Qed.

(* 0x83880: bltz s9 -> 0x8389c, then a0 := -8 to 0x838a0; else 0x83884 .. 0x843a4: a0 := res (s10),
   a1 := x (s2), jal check_keys *)
Lemma br_blk_cells_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) rcv,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 25 = w64 rcv -> - 2 ^ 31 <= rcv < 2 ^ 31 ->
SRr rsegs W (cfg_at rsegs BR_CELLS_RET regs memc mdc)
 (fun W2 c2 =>
  (rcv < 0 /\ hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_XOUT [10]%bv
     (fun _ => False) (fun W2 regs2 mem2 => getr regs2 10 = w64 (-8)) W2 c2) \/
  (0 <= rcv /\ hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_CK_KEYS [1; 10; 11]%bv
     (fun _ => False)
     (fun W2 regs2 mem2 => getr regs2 1 = w64 BR_KEYS_RET /\ getr regs2 10 = getr regs 26 /\
        getr regs2 11 = getr regs 18) W2 c2)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs rcv HJ H25 Hrc.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (br_ss0_ok W regs memc BR_CELLS_RET) as HS.
unfold cfg_at. change (w64 BR_CELLS_RET) with (Z_to_bv 64 BR_CELLS_RET).
assert (HB : forall b, branch_taken BC_LT (sv_denot (Ereg regs []) (SOff 25 0)) (sv_denot (Ereg regs []) (SLit 0)) = b ->
  if b then rcv < 0 else 0 <= rcv).
{ intros b Hb. rewrite (br_atom regs [] 25 25%bv eq_refl), H25 in Hb.
  change (sv_denot (Ereg regs []) (SLit 0)) with (Z_to_bv 64 0) in Hb.
  unfold w64 in Hb. rewrite (br_lt0 rcv Hrc) in Hb. subst b. destruct (Z.ltb_spec rcv 0); lia. }
srr_branch_with br_tbl_ok HS.
- (* taken: rc < 0, through 0x8389c to 0x838a0 *)
  pose proof (HB true Hc) as Hlt. cbv iota in Hlt.
  aj_run br_tbl_ok HS HJ; [awr_ok_tac|].
  apply SRr_ret. left. split; [exact Hlt|].
  br_post_ro_body HS HJ HFr regs ([10]%bv : list (bv 5)).
  rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
  lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e1 end.
  cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- (* not taken: 0 <= rc, 0x83884 .. 0x843a4 *)
  pose proof (HB false Hc) as Hge. cbv iota in Hge.
  aj_run br_tbl_ok HS HJ; [awr_ok_tac|].
  apply SRr_ret. right. split; [exact Hge|].
  br_post_ro_body HS HJ HFr regs ([1; 10; 11]%bv : list (bv 5)).
  rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
  lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ /\ _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) 1%bv) in change (sr_get (ss_regs ss) 1%bv) with e1;
    let e2 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e2;
    let e3 := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e3 end.
  split; [reflexivity|]. split; apply br_atom; reflexivity.
Qed.

(* 0x83890 .. 0x84438: a0 := res (s10), a1 := x (s2), jal check_refusal *)
Lemma br_blk_keys_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
SRr rsegs W (cfg_at rsegs BR_KEYS_RET regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_CK_REFUSAL [1; 10; 11]%bv
   (fun _ => False)
   (fun W2 regs2 mem2 => getr regs2 1 = w64 BR_REF_RET /\ getr regs2 10 = getr regs 26 /\
      getr regs2 11 = getr regs 18)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs HJ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (br_ss0_ok W regs memc BR_KEYS_RET) as HS.
unfold cfg_at. change (w64 BR_KEYS_RET) with (Z_to_bv 64 BR_KEYS_RET).
aj_run br_tbl_ok HS HJ; [awr_ok_tac|].
br_post_ro HS HJ HFr regs ([1; 10; 11]%bv : list (bv 5)).
rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ /\ _ =>
  let e1 := eval vm_compute in (sr_get (ss_regs ss) 1%bv) in change (sr_get (ss_regs ss) 1%bv) with e1;
  let e2 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e2;
  let e3 := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e3 end.
split; [reflexivity|]. split; apply br_atom; reflexivity.
Qed.

(* 0x8389c: a0 := -8 *)
Lemma br_blk_li : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
SRr rsegs W (cfg_at rsegs BR_REF_RET regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BR_XOUT [10]%bv
   (fun _ => False) (fun W2 regs2 mem2 => getr regs2 10 = w64 (-8))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs HJ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (br_ss0_ok W regs memc BR_REF_RET) as HS.
unfold cfg_at. change (w64 BR_REF_RET) with (Z_to_bv 64 BR_REF_RET).
aj_run br_tbl_ok HS HJ; [awr_ok_tac|].
br_post_ro HS HJ HFr regs ([10]%bv : list (bv 5)).
rewrite !(st_ok_restrict_reg rsegs _ _ _ _ _ HS).
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) _) = _ =>
  let e1 := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with e1 end.
cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

End d.
End b.
