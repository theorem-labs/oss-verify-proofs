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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 325 of its 361 lines of code are new or changed and 417 lines of the source are left out. *)
(* Segment 3 of the image-B walk of reac_segconf_declared, its second half (reac_segconf_declared_s3.v has the first):
   from the return of reac_declared_vlan_add (0x8a070) to the latch KT (0x8a0b4) or the join KX (0x8a0fc).
     0x8a070 bltz a0            add answered -1: to 0x8a1d8
     0x8a1d8 li a0,-8; ld s11,48(s1); sb a0,4/5/8(s11) (vid and parent out of scope); li a0,-1; sd a0,88(s1);
             j 0x8a0fc (KX, the result -1)
     0x8a074 lw a1,88(s1); add a2,a1,a0; addw a0,a1,a0; sd a2,88(s1)   added += r
     0x8a084 bne a0,a2          the UBSan trap 0x8a1f8 on a 32-bit overflow of added + r: not taken, added <= i <= 31
                                and r is 0 or 1 (dcl_add_rv_nonneg)
     0x8a088 .. 0x8a098 the register moves back, ld s11,48(s1); 0x8a09c ld a3,80(s1) (~c); li a4,32;
     0x8a0a4 .. 0x8a0b0 sb -8 into the frame's shadow bytes 4, 5, 8; KT at pass i. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaCall PaNoChain
PaLibG PaLibF PaCallRun SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem reac_segconf_declared_s3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return point of the call of reac_declared_vlan_add at +0x1f0 (0x8a06c) *)
Definition DCS3_RET : Z := AF_reac_segconf_declared + 0x1f4.
(* the symbolic state after the call: the slots 48 (the frame's shadow, atom 32), 80 (~c, atom 34) and 88 (added,
   atom 33, writable) of s1, and the frame's shadow bytes 4 .. 8 (writable), based on atom 32 *)
Definition dcs3_s1B : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 96 88 96
    [YP09.mkChunk 48 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 8 (SOff 33 0))].
Definition dcs3_shB : YP09.region := YP09.mkRegion (Some 32%nat) 4 9 4 9 [].
Definition dcs3_ssB (G : facts) : sstate := mkSS DCS3_RET sr_atoms [dcs3_s1B; dcs3_shB] None G.

Lemma dcs3_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition dcs3_EB (regs : bvmap 5 word) (F added cc : Z) : env :=
  Eimg (Ereg regs [w64 (SB + F / 8); w64 added; w64 (2 ^ 64 - 1 - cc)]).
Lemma dcs3_seedB : forall (W : world SEGS) mem (regs : bvmap 5 word) s1 F added cc G,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 96 <= 2 ^ 64 -> 0 <= F -> SB + F / 8 + 9 <= s1 + 48 ->
  0 <= cc < 2 ^ 64 -> 0 <= added < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 48) = Some (SB + F / 8) -> rdword (rdW W mem) (s1 + 80) = Some (2 ^ 64 - 1 - cc) ->
  rdword (rdW W mem) (s1 + 88) = Some added ->
  (forall o, 88 <= o < 96 -> apresent (w_H W) mem (s1 + o)) ->
  (forall o, 4 <= o < 9 -> apresent (w_H W) mem (SB + F / 8 + o)) ->
  facts_ok (dcs3_EB regs F added cc) G ->
  st_ok_pi SEGS VAL (dcs3_EB regs F added cc) (dcs3_ssB G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS3_RET)) mem (seg_rom SEGS))).
Proof using.
intros W mem regs s1 F added cc G H9 Hs0 Hs1 HF0 HF1 Hcc Had R48 R80 R88 Hp1 Hp2 HG.
set (E := dcs3_EB regs F added cc).
assert (HF8 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm0. subst E. unfold dcs3_EB. apply ew_Eimg_Ereg_nat. exact Hm0. }
assert (X : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 (SB + F / 8); w64 added; w64 (2 ^ 64 - 1 - cc)] (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold dcs3_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U9 : base_val E (Some 9%nat) = s1).
{ cbn [base_val]. rewrite (EEo 9%nat 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U32 : base_val E (Some 32%nat) = SB + F / 8).
{ cbn [base_val]. pose proof (X 0%nat ltac:(lia)) as X0. cbn [Nat.add nth] in X0. rewrite X0. unfold w64. apply unsigned_lit_small. unfold SB in *. lia. }
assert (D : forall j z, (j < 3)%nat -> nth j [w64 (SB + F / 8); w64 added; w64 (2 ^ 64 - 1 - cc)] (Z_to_bv 64 0) = w64 z ->
  sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 z).
{ intros j z Hj Hz. cbn [sv_denot]. rewrite (X j Hj), Hz, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite restrict_mkst_fx. unfold dcs3_ssB. apply pa_entry_st_ok_full.
- subst E. unfold dcs3_EB. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs3_s1B, dcs3_shB. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hp1; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 48 8 (SOff 32 0) (SB + F / 8)); [exact (D 0%nat _ ltac:(lia) eq_refl) | cbn; unfold SB in *; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R48.
    * apply (chunk_ok_val SEGS E _ s1 80 8 (SOff 34 0) (2 ^ 64 - 1 - cc)); [exact (D 2%nat _ ltac:(lia) eq_refl) | cbn; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R80.
    * apply (chunk_ok_val SEGS E _ s1 88 8 (SOff 33 0) added); [exact (D 1%nat _ ltac:(lia) eq_refl) | cbn; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R88.
  + rewrite U32. split; [unfold SB in *; lia|]. split; [unfold SB in *; lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hp2; lia|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold dcs3_s1B, dcs3_shB, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  split; [split; [right; lia | exact I] | split; exact I].
- exact HG.
Qed.
(* an 8-byte value chunk of the first region of a symbolic state, read back from the memory *)
Lemma dcs3_rd_chunk8 : forall E ss (H : word -> bool) ms r nb off e,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some r ->
  YP09.r_base r = Some nb -> In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  rdword (aview SEGS H (ms_mem ms)) (bv_unsigned (ew E nb) + off) = Some (U E e).
Proof using.
intros E ss H ms r nb off e HS Hi Hb Hin.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) 0 r HS Hi) as (_ & _ & _ & HC).
rewrite Forall_forall in HC. specialize (HC _ Hin).
change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in HC.
rewrite Hb in HC. cbn [base_val] in HC.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Rn. change (bv_modulus 64) with (2 ^ 64) in Rn.
apply (rdword_of_val_mem SEGS); [|unfold U; exact Rn].
apply (val_of_chunk_ok SEGS E _ _ off 8 e (U E e) HC).
- unfold U. symmetry. apply Z_to_bv_bv_unsigned.
- unfold U. cbn. lia.
- cbn. lia.
Qed.
(* the bytes the tail's runs write: 88(s1) .. 96(s1) and the frame's shadow bytes 4 .. 8 *)
Definition dcs3_W (c : dcx) (a : Z) : Prop :=
  (dc_s1 c + 88 <= a < dc_s1 c + 96) \/ (SB + dc_F c / 8 + 4 <= a < SB + dc_F c / 8 + 9).

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation PRE := (dc_pre B DC_STK RLO RHI GOTW GUARD).
#[local] Notation JR c S3 W3 mem3 md3 k := (ajournal SEGS B DC_STK (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c)
  (x_mem c) (x_md c) [(1, x_fpos c)] (x_ly c) S3 W3 mem3 md3 k).
(* the state at the return of the add call (0x8a070) *)
Record dcs3_R (c : dcx) (i : nat) (ti : list (list Z * Z)) (added : Z) (p : list Z) (v : Z)
  (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop := mkDCS3R {
  r_j : JR c S2 W2 mem2 md2 0;
  r_un : dc_un B c (x_ly c) S2;
  r_tab : dc_tab c (snd (vlan_add ti (x_max c) p v)) W2 mem2;
  r_tab0 : (length (x_tb c) <= length ti)%nat;
  r_i : (i < length (dc_segs c))%nat;
  r_loop : dc_loop c i ti added;
  r_ign : rs_ignore (nth i (dc_segs c) rseg_d) = false;
  r_spl : vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v);
  r_a0 : getr regs2 10 = w64 (fst (vlan_add ti (x_max c) p v));
  r_sp : getr regs2 2 = w64 (dc_s1 c);
  r_gp : getr regs2 3 = w64 (as_gp B);
  r_tp : getr regs2 4 = w64 (as_tp B);
  r_s0 : getr regs2 8 = w64 (dc_sp0 c);
  r_s1 : getr regs2 9 = w64 (dc_s1 c);
  r_18 : getr regs2 18 = w64 (356 * Z.of_nat i);
  r_19 : getr regs2 19 = w64 (dc_F c + 32);
  r_20 : getr regs2 20 = w64 SB;
  r_21 : getr regs2 21 = w64 (dc_F c + 32);
  r_22 : getr regs2 22 = w64 (x_c c + 356 * Z.of_nat i);
  r_23 : getr regs2 23 = w64 (SB + (x_c c + DC_RC_N) / 8);
  r_24 : getr regs2 24 = w64 (Z.of_nat i);
  r_25 : getr regs2 25 = w64 (x_c c + 356 * Z.of_nat i + DC_IGN);
  r_26 : getr regs2 26 = w64 (dc_F c + 64);
  r_27 : getr regs2 27 = w64 (x_c c + DC_RC_N);
  r_saved : forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W2 mem2) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)));
  r_f32 : rdword (rdW W2 mem2) (dc_s1 c + 32) = Some (dc_F c);
  r_f40 : rdword (rdW W2 mem2) (dc_s1 c + 40) = Some (dc_F c);
  r_ftab : rdword (rdW W2 mem2) (dc_s1 c + 56) = Some (dc_a1 c);
  r_fmax : rdword (rdW W2 mem2) (dc_s1 c + 64) = Some (dc_a2 c);
  r_fn : rdword (rdW W2 mem2) (dc_s1 c + 72) = Some (dc_a3 c);
  r_flag : rdword (rdW W2 mem2) (dc_F c + 120) = Some (dc_FL c);
  r_l48 : rdword (rdW W2 mem2) (dc_s1 c + 48) = Some (SB + dc_F c / 8);
  r_l80 : rdword (rdW W2 mem2) (dc_s1 c + 80) = Some (2 ^ 64 - 1 - x_c c);
  r_l88 : rdword (rdW W2 mem2) (dc_s1 c + 88) = Some added }.

(* the writable windows of the tail's runs: 88(s1) .. 96(s1), in this call's stack window, and the frame's shadow bytes
   4 .. 8, in its own frame's shadow; needs U9, U32 and F128 of the tail's context *)
Ltac dcs3_awr_tac :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end;
  lazymatch goal with U9 : bv_unsigned (ew _ 9) = dc_sp0 ?c + _ |- _ =>
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := dc_s1 c - dc_sp0 c);
    [reflexivity | exact U9 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  eapply awr_ok_cons_gen with (n := 32%nat) (b := SB + dc_F c / 8);
    [reflexivity | eassumption |
     intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold awr_byte; right; right; right; left;
     exists 1, (x_fpos c); split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
     replace (fs_frame_bytes 1) with 128 by (vm_compute; reflexivity);
     change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c); unfold SB, SHADOW_OFF in *; lia
    | apply awr_ok_nil] end.
(* the reader after a run of the tail, from the windows its regions can write *)
Ltac dcs3_heq E W2 mem2 c HFr U9 U32 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) E _ (w_H W2) mem2 _ (dcs3_W c) HFr); [| exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
    change (In (b, wlo, whi) w) in Hin end;
  cbn [In] in Hin; unfold dcs3_W;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?U9, ?U32 in Hx; lia|]);
  destruct Hin.
Lemma dcs3_tail : forall c i ti added p v S2 W2 regs2 mem2 md2, PRE c ->
  from_KT B DC_STK c i -> from_KX B DC_STK c -> dcs3_R c i ti added p v S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + DCS3_RET)) mem2 (seg_rom SEGS)) md2) (dc_post B DC_STK c).
Proof using.
intros c i ti added p v S2 W2 regs2 mem2 md2 HP HKT HKX HR.
destruct HR as [HJ HUN HTAB HTB0 Hi HLOOP Hign Hspl R10 R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
  RSV RF32 RF40 RFT RFM RFN RFL L48 L80 L88].
pose proof HP as [HAFN _ _ HC64 _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & (bs & _ & _ & Hle32 & _) & _).
destruct (dcs3_stk B RLO RHI GOTW GUARD c HP) as (Hal16 & Hceil & Hslo & Htop & H47 & Hs1m & Hs1 & DS & DA).
destruct (dcs3_frame B c S2 W2 mem2 md2 0 HJ) as (HinF & HF0 & HFc & HFapp & HF64).
pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 HinF) as (_ & _ & _ & Hshp).
assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in Hshp.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hshp.
pose proof HLOOP as [_ Hadd]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hadd31 : 0 <= added <= 31) by (unfold dc_segs in Hi; lia).
pose proof (dcl_add_rv ti (x_max c) p v) as Hrv3.
assert (Hsb : SB + dc_F c / 8 + 16 <= alloc_ceiling).
{ unfold SB. assert (dc_F c / 8 <= dc_F c) by (apply Z.div_le_upper_bound; lia). lia. }
pose proof (dcs3_res_neg c i ti added p v Hi HLOOP Hign Hspl) as HRN.
pose proof (dcs3_loop_next c i ti added p v Hi HLOOP Hign Hspl) as HLN.
pose proof (dcl_add_rv_nonneg ti (x_max c) p v) as H01.
remember (vlan_add ti (x_max c) p v) as VA eqn:HVA. destruct VA as [rv ti']. cbn [fst snd] in *. clear HVA.
set (E := dcs3_EB regs2 (dc_F c) added (x_c c)).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold dcs3_EB; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs2 rr)
  by (intros m rr Hm0; subst E; unfold dcs3_EB; apply ew_Eimg_Ereg_nat; exact Hm0).
assert (U9 : bv_unsigned (ew E 9) = dc_sp0 c + (dc_s1 c - dc_sp0 c)).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (X32 : ew E 32 = w64 (SB + dc_F c / 8))
  by (subst E; unfold dcs3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (X33 : ew E 33 = w64 added)
  by (subst E; unfold dcs3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (X34 : ew E 34 = w64 (2 ^ 64 - 1 - x_c c))
  by (subst E; unfold dcs3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (U32 : bv_unsigned (ew E 32) = SB + dc_F c / 8).
{ rewrite X32. unfold w64. apply unsigned_lit_small. assert (0 <= dc_F c / 8) by (apply Z.div_pos; lia). unfold SB in *. lia. }
assert (HSEED : forall G, facts_ok E G ->
  st_ok_pi SEGS VAL E (dcs3_ssB G) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + DCS3_RET)) mem2 (seg_rom SEGS)))).
{ intros G HG. exact (dcs3_seedB W2 mem2 regs2 (dc_s1 c) (dc_F c) added (x_c c) G R9 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) HC64 ltac:(lia) L48 L80 L88 ltac:(intros o Ho; apply Hpres2; lia)
    ltac:(intros o Ho; apply (proj1 (Hshp o ltac:(lia)))) HG). }
(* the facts every cut needs, after a run that writes only 88(s1) .. 96(s1) and the frame's shadow bytes 4 .. 8 *)
assert (HD1 : 0 <= dc_F c / 8) by (apply Z.div_pos; lia).
assert (HD3 : dc_F c / 8 <= 17592185978880).
{ apply Z.div_le_upper_bound; [lia|]. pose proof alloc_ceiling_val as [[CL CH] _]. lia. }
pose proof HP as [_ _ _ _ _ HT64 _ _ _ HN64 HDP' _ _].
destruct HDP' as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Na0 & Na63 & _) & _).
destruct (dcs3_far_tab B RLO RHI GOTW GUARD c S2 W2 mem2 md2 0 HP HJ HUN) as (FT & Htc & _).
pose proof (dcs3_far_n B RLO RHI GOTW GUARD c S2 W2 mem2 md2 0 HP HJ HUN) as FN.
assert (HSAFE : forall a, dcs3_W c a -> dcs3_safe c a).
{ intros a [Ha | Ha]; unfold dcs3_safe; [left; lia | right; right; lia]. }
assert (HTABK : forall mem', (forall a, 0 <= a < 2 ^ 64 -> ~ dcs3_W c a -> rdW W2 mem' a = rdW W2 mem2 a) ->
  dc_tab c ti' W2 mem').
{ intros mem' HE. apply (dcs3_tab_ext c ti' W2 W2 mem2 mem'); [|exact HTAB].
  intros x Hx. apply HE.
  - destruct Hx as [Hx | Hx]; unfold seg_spec.RVLAN_SIZE in *; lia.
  - intros Hw. destruct Hx as [Hx | Hx];
      [exact (dcs3_safe_far c _ _ x HFapp FT (HSAFE x Hw) Hx) | exact (dcs3_safe_far c _ _ x HFapp FN (HSAFE x Hw) Hx)]. }
assert (HFIK : forall regs' mem' md', JR c S2 W2 mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ dcs3_W c a -> rdW W2 mem' a = rdW W2 mem2 a) ->
  getr regs' 2 = w64 (dc_s1 c) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  getr regs' 8 = w64 (dc_sp0 c) -> getr regs' 9 = w64 (dc_s1 c) -> getr regs' 27 = w64 (SB + dc_F c / 8) ->
  dc_fi B DC_STK c 0 (x_ly c) S2 W2 regs' mem' md').
{ intros regs' mem' md' HJ' HE T2 T3 T4 T8 T9 T27.
  assert (RK : forall a, (forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ dcs3_W c (a + k)) ->
    rdword (rdW W2 mem') a = rdword (rdW W2 mem2) a).
  { intros a Ha. apply rdword_ext. intros k Hk. destruct (Ha k Hk). apply HE; assumption. }
  constructor; [exact HJ' | exact T2 | exact T3 | exact T4 | exact T8 | exact T9 | exact T27 | | | | | | | ].
  - intros j r Hj. rewrite RK; [exact (RSV j r Hj)|].
    assert (Hj13 : (j < 13)%nat).
    { pose proof (proj1 (nth_error_Some dc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
      change (length dc_saved) with 13%nat in Hl. exact Hl. }
    intros k Hk. unfold dcs3_W. split; lia.
  - rewrite RK; [exact RF32 | intros k Hk; unfold dcs3_W; split; lia].
  - rewrite RK; [exact RF40 | intros k Hk; unfold dcs3_W; split; lia].
  - rewrite RK; [exact RFT | intros k Hk; unfold dcs3_W; split; lia].
  - rewrite RK; [exact RFM | intros k Hk; unfold dcs3_W; split; lia].
  - rewrite RK; [exact RFN | intros k Hk; unfold dcs3_W; split; lia].
  - rewrite RK; [exact RFL|]. intros k Hk. unfold dcs3_W, SB in *. split; [lia|].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
destruct (Z_lt_le_dec rv 0) as [Hneg | Hnn].
- (* add answered -1: 0x8a1d8 .. KX *)
  assert (Erv : rv = -1) by lia.
  assert (R10' : getr regs2 10 = Z_to_bv 64 (2 ^ 64 - 1))
    by (rewrite R10, Erv; unfold w64; apply bv_eq; vm_compute; reflexivity).
  pose proof (st_ok_pi_pin_reg' E _ _ 10%bv (2 ^ 64 - 1) (HSEED (mkFacts [] [] []) ltac:(split; [exact I | split; exact I]))
    R10' eq_refl) as HS.
  paj_run_to_shc RUNTOP HS HJ DC_KX.
  { dcs3_awr_tac. }
  set (mdk := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdk.
  assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ dcs3_W c a -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
    by (dcs3_heq E W2 mem2 c HFr U9 U32).
  assert (G88 : rdword (rdW W2 (ms_mem ms)) (dc_s1 c + 88) = Some (2 ^ 64 - 1)).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 0 (ss_mem ssx) dcs3_s1B) in
      pose proof (dcs3_rd_chunk8 Ex ssx (w_H W2) msx r1 9%nat 88 (SLit 18446744073709551615) HS
        ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [In YP09.r_chunks]; auto 20)) as G end.
    rewrite U9 in G. replace (dc_sp0 c + (dc_s1 c - dc_sp0 c) + 88) with (dc_s1 c + 88) in G by lia.
    rewrite G. rewrite U_SLit. reflexivity. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (27%bv : bv 5) T27.
  rewrite (EEo 2%nat 2%bv eq_refl), R2 in T2. rewrite (EEo 3%nat 3%bv eq_refl), R3 in T3.
  rewrite (EEo 4%nat 4%bv eq_refl), R4 in T4. rewrite (EEo 8%nat 8%bv eq_refl), R8 in T8.
  rewrite (EEo 9%nat 9%bv eq_refl), R9 in T9. rewrite X32 in T27.
  pmkst HS.
  pose proof (HRN Hneg) as HRES.
  apply (HKX (x_ly c) S2 W2 (ms_regs ms) (ms_mem ms) mdk). unfold INV_KX.
  split; [exact (HFIK _ _ _ HJ HEQ T2 T3 T4 T8 T9 T27)|].
  split; [exact HUN|].
  rewrite HRES. cbn [fst snd].
  split; [exact (HTABK _ HEQ)|].
  split; [lia|]. rewrite G88. reflexivity.
- (* add answered 0 or 1: the count update, the trap branch decided by the bounds, the moves back; KT *)
  pose proof (H01 ltac:(lia)) as R01.
  assert (HG : facts_ok E (mkFacts [(33%nat, mkAF 0 31 0); (10%nat, mkAF 0 1 0)] [] [])).
  { split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
    - apply (dcs3_afact E 33%nat added); [exact X33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    - apply (dcs3_afact E 10%nat rv); [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  pose proof (HSEED _ HG) as HS.
  paj_run_to_shc RUNTOP HS HJ DC_KT.
  { dcs3_awr_tac. }
  set (mdk := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdk.
  assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ dcs3_W c a -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
    by (dcs3_heq E W2 mem2 c HFr U9 U32).
  assert (G88 : rdword (rdW W2 (ms_mem ms)) (dc_s1 c + 88) = Some (added + rv)).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 0 (ss_mem ssx) dcs3_s1B) in
      pose proof (dcs3_rd_chunk8 Ex ssx (w_H W2) msx r1 9%nat 88 (SAlu ALU_ADD (SOff 10 0) (SOff 33 0)) HS
        ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [In YP09.r_chunks]; auto 20)) as G end.
    rewrite U9 in G. replace (dc_sp0 c + (dc_s1 c - dc_sp0 c) + 88) with (dc_s1 c + 88) in G by lia.
    rewrite G. f_equal.
    rewrite U_SAlu.
    rewrite (U_atom E 10 rv) by first [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | lia].
    rewrite (U_atom E 33 added) by first [exact X33 | lia].
    cbn [zalu_raw]. rewrite zcanon_small by lia. lia. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (27%bv : bv 5) T27. prreg HS (13%bv : bv 5) T13. prreg HS (14%bv : bv 5) T14.
  prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EEo 2%nat 2%bv eq_refl), R2 in T2. rewrite (EEo 3%nat 3%bv eq_refl), R3 in T3.
  rewrite (EEo 4%nat 4%bv eq_refl), R4 in T4. rewrite (EEo 8%nat 8%bv eq_refl), R8 in T8.
  rewrite (EEo 9%nat 9%bv eq_refl), R9 in T9. rewrite X32 in T27. rewrite X34 in T13.
  rewrite (EEo 18%nat 18%bv eq_refl), R18 in T18. rewrite (EEo 21%nat 21%bv eq_refl), R21 in T19.
  rewrite (EEo 23%nat 23%bv eq_refl), R23 in T20. rewrite (EEo 20%nat 20%bv eq_refl), R20 in T21.
  rewrite (EEo 22%nat 22%bv eq_refl), R22 in T22. rewrite (EEo 27%nat 27%bv eq_refl), R27 in T23.
  rewrite (EEo 24%nat 24%bv eq_refl), R24 in T24. rewrite (EEo 25%nat 25%bv eq_refl), R25 in T25.
  rewrite (EEo 26%nat 26%bv eq_refl), R26 in T26.
  pmkst HS.
  apply (HKT ti' (added + rv) (x_ly c) S2 W2 (ms_regs ms) (ms_mem ms) mdk). unfold INV_KT.
  split; [exact (HFIK _ _ _ HJ HEQ T2 T3 T4 T8 T9 T27)|].
  split; [exact HUN|].
  split; [exact (HTABK _ HEQ)|].
  split; [exact Hi|].
  split; [exact (HLN ltac:(lia))|].
  split; [unfold dc_lregs;
    refine (conj T24 (conj T22 (conj T25 (conj T23 (conj T20 (conj T19 (conj T26 (conj T21 T18))))))))|].
  split; [unfold dc_aregs; split; [exact T13 | exact T14]|].
  unfold dc_lslots. split; [|split; [|exact G88]].
  + rewrite <- L48. apply rdword_ext. intros k Hk. apply HEQ; [lia|]. unfold dcs3_W. lia.
  + rewrite <- L80. apply rdword_ext. intros k Hk. apply HEQ; [lia|]. unfold dcs3_W. lia.
Qed.
End e.
End f.
End d.
