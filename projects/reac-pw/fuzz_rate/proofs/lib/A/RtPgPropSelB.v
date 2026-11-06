(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state, save-slot region, run / keep / leaf chain and write obligations, reused by Require) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_refuse_code 0x82e6c against lib/A/RPgCSpec.v's rl_refuse_code_specX on the concrete image lib/A/Img0.v rsegs, with its own code table (23 words from 0x82e6c), the a0 clause of lib/A/RPgCfgChanges.v's cfg_leaf and its cfg_branch split, and the .got-slot / shadow-offset-cell regions of proofs/libreac/fuzz_knock/lib/A/ACeh.v got_region / bcell_region at origin/ossv/recipes 6ebe35ba632 (with lib/A/APgRt.v's al_const / chunk_ok_val / val_mem_of_rdword proofs of them); new: the regions of the two shadow bytes of the table and of the table itself, and the split on a0 (r >= 2: one branch; r = 0, r = 1: a0 a literal). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v and lib/A/RPgCheck.v at 77f59d02b01
   (the save-slot region, its write obligation awr_stk / kwr_stk, the .got-slot and shadow-offset-cell regions with
   their proofs from AR's constant law, the zero-shadow-byte lemma, the overrides of the entry registers, the run /
   keep / branch chain and the `ret` leaf) for reac-pw/fuzz_rate's image A (fuzz_rate.asan): it walks check_list
   0x837a8 against lib/A/RtPgCSpec.v's rt_check_list_specX on the image module's loaded segments, with the plumbing
   lemmas of lib/A/RtPgLeaf.v; new: the regions of closed_list's 12 bytes and of its two shadow bytes (the second
   one any value range_addressable allows at offset 11), the four cases on hz and the five on that shadow byte, the
   two loops run with every iteration's compare decided or split, and the mask tail split on the three bit tests. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheckList.v, with its module names changed; 548 of its 618 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSelB.v (the sel block pa_sel) and the sel
   piece pa_piece_sel of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v, both at a529a88a6181, for reac-pw/fuzz_rate image A:
   rate's pcs, registers (in.n in s8, the shadow offset in s2, the shadow address of pp + 0x4000 in s6, pp + 0x4000
   in s7) and real-frame cells (i R+0xf8, the cursor R+0x100, sh R+0xd8, -0x3ffd R+0x130); with no input left the
   block stores nothing but i (rate's code does not write in.n there); the block post is lib/A/RtPgSteps.v rts_post;
   the cut lists are lib/A/RtPgSeg.v's. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the sel block N 0x80e10 of
   LLVMFuzzerTestOneInput's property loop, to SEL7 0x80e6c (sh = 7) or SELK 0x81018, as a block lemma over
   lib/A/RtPgPropKit.v, and the piece rs_piece_W4_sel_stmt (N -> SEL7 / SELK) of lib/A/RtPgSeg.v. Proves no function
   (kind: segment lemma).
     0x80e10 sd a6,0xf8(s1)                      i
     0x80e14 beqz s8                             no input left: 0x80e44 a1 = 0; -> 0x80e48
     0x80e18 ld a0,0x100(s1); 0x80e1c .. 0x80e2c the check of the byte at the cursor (EQ-J: lb a2,0(sh); beqz a2,+8;
                                                 j 0x82540 = andi a1,a0,7; bge a1,a2 -> report; j 0x80e30)
     0x80e30 lbu a1,0(a0); a0 + 1; s8 - 1; sd a0,0x100(s1); j 0x80e48
     0x80e48 the check of pp->len (lbu a0,0(s6); beqz a0,+8); 0x80e54 ld a0,0(s7) = len; ld a2,0x130(s1);
             a2 = len - 0x3ffd; 0x80e60 ld a3,0xd8(s1) = sh; a4 = 7; 0x80e68 bne a3,a4 -> 0x81018, else 0x80e6c.
   The walk splits on nl = 0 before its entry state. With nl > 0 the input byte b is a region based at the cursor's
   atom and its shadow byte s a region based at a fresh atom (the cursor's shadow address, tied to the cursor by an
   alias fact); s = 0 runs on, s <> 0 goes through 0x82540, whose report arm dies by saddr_ok. pp's len cell is a
   region based at atom 27, and the shadow entry of the whole pp block makes the check of pp->len free. The two
   stores are the write windows of two 8-byte regions based at atom 9 (R). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgPropKit RtPgPropLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgSteps.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the entry states ----
   env slots (pa_extra): 32 K, 33 nl, 34 cur, 35 sh, 36 plen, 37 b, 38 the cursor's shadow address, 39 its byte s *)
Definition pa_s_SH : list shent := [mkSHE 27 0 19744].
(* s6 = the shadow address of pp + 0x4000, s7 = pp + 0x4000, s2 = K, s8 = nlv (in.n) *)
Definition pa_s_sr (nlv : sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (22%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0x4000) (SLit 3)) (SOff 32 0)))
    (23%bv : bv 5) (SOff 27 0x4000)) (18%bv : bv 5) (SOff 32 0)) (24%bv : bv 5) nlv.
(* the four cells of R the block reads or writes (each write window exactly its 8 bytes) and pp's len cell *)
Definition pa_s_rd8 : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xe0 0 0 [ YP09.mkChunk 0xd8 (CVal 8 (SOff 35 0)) ].
Definition pa_s_rf8 : YP09.region := YP09.mkRegion (Some 9%nat) 0xf8 0x100 0xf8 0x100 [].
Definition pa_s_r100 : YP09.region := YP09.mkRegion (Some 9%nat) 0x100 0x108 0x100 0x108 [ YP09.mkChunk 0x100 (CVal 8 (SOff 34 0)) ].
Definition pa_s_r130 : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0 [ YP09.mkChunk 0x130 (CVal 8 (SLit (-16381))) ].
Definition pa_s_rlen : YP09.region := YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0 0 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 36 0)) ].
(* the input byte at the cursor and its shadow byte *)
Definition pa_s_rin : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 37 0)) ].
Definition pa_s_rcell : YP09.region := YP09.mkRegion (Some 38%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 39 0)) ].
(* R lies in the stack above the allocator's ceiling; pp's upper bound keeps the shadow of its block in the span *)
Definition pa_s_G1 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 4096 140737479946976 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (33%nat, mkAF 1 9223372036854775807 0); (34%nat, mkAF 1 9223372036854775807 0); (35%nat, mkAF 0 7 0);
    (36%nat, mkAF 0 5440 0); (37%nat, mkAF 0 255 0); (39%nat, mkAF 0 7 0) ] []
  [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0), SOff 38 0) ].
Definition pa_s_G0 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 4096 140737479946976 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (35%nat, mkAF 0 7 0); (36%nat, mkAF 0 5440 0) ] [] [].
Definition ss_s1 : sstate :=
  mkSS PA_N (pa_s_sr (SOff 33 0)) [pa_s_rd8; pa_s_rf8; pa_s_r100; pa_s_r130; pa_s_rlen; pa_s_rin; pa_s_rcell] None pa_s_G1.
Definition ss_s0 : sstate :=
  mkSS PA_N (pa_s_sr (SLit 0)) [pa_s_rd8; pa_s_rf8; pa_s_r100; pa_s_r130; pa_s_rlen] None pa_s_G0.

(* ---- small facts ---- *)
(* an override of a register by a value it already has keeps regs_ok *)
Lemma pa_s_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
(* the value of the shadow address expression (x >> 3) + k *)
Lemma pa_s_shU : forall E a k, U E k + U E a / 8 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL a (SLit 3)) k) = U E k + U E a / 8.
Proof.
intros E a k Hlt. rewrite !U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (U_range E a) as Ha. pose proof (U_range E k) as Hk. unfold M64 in *.
assert (0 <= U E a / 8) by (apply Z.div_pos; lia).
rewrite (zcanon_id (U E a / 8)) by (unfold M64; lia).
rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pa_s_den : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma pa_s_Uoff : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
U E (SOff n c) = x + c.
Proof. intros E n x c H Hx Hc. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. Qed.
Lemma pa_s_doff : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof. intros E n x c H Hx. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
(* x / 8 as an atom lia can use *)
Lemma pa_s_div8 : forall x, 0 <= x -> 0 <= x / 8 /\ 8 * (x / 8) <= x /\ x < 8 * (x / 8) + 8.
Proof.
intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
split; [apply Z.div_pos; lia | lia].
Qed.
(* the entry registers: sr_atoms with s6, s7, s2 and s8 as the shadow address of pp + 0x4000, pp + 0x4000, K and nlv *)
Lemma pa_s_regs_ok : forall regs l pp nlv, getr regs 27 = w64 pp -> 0 <= pp < 2 ^ 47 ->
getr regs 23 = w64 (pp + 0x4000) -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 18 = w64 SHADOW_OFF ->
sv_denot (Ereg regs (pa_extra l)) nlv = getr regs 24 ->
regs_ok (Ereg regs (pa_extra l)) (pa_s_sr nlv) regs.
Proof.
intros regs l pp nlv H27 Hpp H23 H22 H18 H24. set (E := Ereg regs (pa_extra l)) in *.
assert (W27 : ew E 27 = Z_to_bv 64 pp) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
unfold pa_s_sr. apply pa_s_override; [apply pa_s_override; [apply pa_s_override; [apply pa_s_override;
  [apply regs_ok_Ereg | | ] | | ] | | ] | | ].
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H22. unfold w64, shadow_addr. apply pa_s_den.
  assert (U27 : U E (SOff 27 0x4000) = pp + 0x4000) by (apply (pa_s_Uoff E 27 pp 0x4000 W27); lia).
  pose proof (pa_s_div8 (pp + 0x4000) ltac:(lia)) as Hpp8.
  assert (Hlt : U E (SOff 32 0) + U E (SOff 27 0x4000) / 8 < 2 ^ 64) by (rewrite U32, U27; unfold SHADOW_OFF; lia).
  rewrite (pa_s_shU E _ _ Hlt), U32, U27. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H23. unfold w64. apply pa_s_doff; [exact W27 | lia].
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H18. unfold w64. rewrite (pa_s_doff E 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia).
  rewrite Z.add_0_r. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- exact H24.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* every register outside clob keeps its entry value: its symbolic value is still the entry one *)
Lemma pa_s_kept : forall E ss ms sr0 regs0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms sr0 regs0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
  rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. exact (HR r).
Qed.
(* an 8-byte value read back out of a region's chunk at the end of a run (the inverse of pa_chunk8) *)
Lemma pa_s_field8 : forall E ss ms i n lo hi wlo whi cs b od e v,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> val_mem rsegs (ms_mem ms) (b + od) 8 v.
Proof.
intros E ss ms i n lo hi wlo whi cs b od e v HS Hi Hn Hc He Hv.
destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hi)) as Hr.
unfold region_ok in Hr. cbn [YP09.r_base YP09.r_chunks base_val] in Hr. destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E _ b od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
End b.

(* ---- the walk's plumbing ---- *)
(* the write windows of a state: the two cells of R, inside the caller's stack allowance *)
Ltac pa_s_awr :=
lazymatch goal with E9 : bv_unsigned (ew ?E 9) = ?Rv |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (Rv - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ]
end.
(* every write window of a state lies in the block's write set *)
Ltac pa_s_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite ?E9 in Hb end; lia | ]);
destruct Hr.
Ltac pa_s_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pa_tbl_ok HS HJ SHOK PAspan stop; [pa_s_awr | ] end.
Ltac pa_s_runb :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok pa_tbl_ok HS HJ SHOK PAspan; [pa_s_awr | ] end.
(* the leaf: rts_post's first eight clauses (RtPgPropKit's pa_leaf, with the registers kept against the entry's
   symbolic registers HR0, which override s2, s6, s7 and s8); the relation is left *)
Ltac pa_s_leaf HR0 :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [eapply (pa_s_kept _ _ ms _ _ (w_H W) _ HS HR0); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.
(* an 8-byte cell of the end state, region i based at b, chunk at od *)
Ltac pa_s_val i b od :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms));
eapply (pa_s_field8 E ss (restrict H ms) i n lo hi wlo whi cs b od); [exact HS | vm_compute; reflexivity | | left; reflexivity | | ]
end end.
(* the relation at the end, nl > 0: a0 = plen, a1 = b, a2 = plen - 0x3ffd, s8 = nl - 1; R+0xf8 = i,
   R+0x100 = cur + 1 (regions 1 and 2 of the end state) *)
Ltac pa_s_rel1 E9 W16 E33 E34 E36 E37 :=
lazymatch type of E9 with bv_unsigned _ = ?Rv =>
cbv beta;
pa_reg (10%bv : bv 5); pa_reg (11%bv : bv 5); pa_reg (12%bv : bv 5); pa_reg (24%bv : bv 5);
refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
[ unfold w64; rewrite (pa_s_doff _ 36 _ 0 E36) by lia; rewrite Z.add_0_r; reflexivity
| unfold w64; rewrite (pa_s_doff _ 37 _ 0 E37) by lia; rewrite Z.add_0_r; reflexivity
| unfold w64; rewrite (pa_s_doff _ 36 _ (-16381) E36) by lia; reflexivity
| unfold w64; rewrite (pa_s_doff _ 33 _ (-1) E33) by lia; reflexivity
| pa_s_val 1%nat Rv 0xf8; [exact E9 | rewrite (pa_s_doff _ 16 _ 0 W16) by lia; rewrite Z.add_0_r; reflexivity | lia]
| pa_s_val 2%nat Rv 0x100; [exact E9 | rewrite (pa_s_doff _ 34 _ 1 E34) by lia; reflexivity | lia] ]
end.
(* the relation at the end, nl = 0: a1 = 0, s8 = 0 (not written), R+0x100 = cur (not written) *)
Ltac pa_s_rel0 E9 W16 E34 E36 :=
lazymatch type of E9 with bv_unsigned _ = ?Rv =>
cbv beta;
pa_reg (10%bv : bv 5); pa_reg (11%bv : bv 5); pa_reg (12%bv : bv 5); pa_reg (24%bv : bv 5);
refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
[ unfold w64; rewrite (pa_s_doff _ 36 _ 0 E36) by lia; rewrite Z.add_0_r; reflexivity
| reflexivity
| unfold w64; rewrite (pa_s_doff _ 36 _ (-16381) E36) by lia; reflexivity
| reflexivity
| pa_s_val 1%nat Rv 0xf8; [exact E9 | rewrite (pa_s_doff _ 16 _ 0 W16) by lia; rewrite Z.add_0_r; reflexivity | lia]
| pa_s_val 2%nat Rv 0x100; [exact E9 | rewrite (pa_s_doff _ 34 _ 0 E34) by lia; rewrite Z.add_0_r; reflexivity | lia] ]
end.
(* 0x80e68 bne a3,a4 (sh against 7): taken -> SELK 0x81018, else SEL7 0x80e6c; run to the target, leaf; the
   relation is left in both goals *)
Ltac pa_s_fin E35 HR0 :=
lazymatch type of E35 with ew _ 35 = Z_to_bv 64 ?shv =>
let Hc7 := fresh "Hc7" in
pa_branch Hc7; rewrite YN3v.branch_ne_U, (pa_s_Uoff _ 35 _ 0 E35), U_SLit, (zcanon_id 7) in Hc7 by (unfold M64; lia);
rewrite Z.add_0_r in Hc7;
first [ apply negb_true_iff, Z.eqb_neq in Hc7 | apply negb_false_iff, Z.eqb_eq in Hc7 ];
[ replace (if shv =? 7 then PA_SEL7 else PA_SELK) with PA_SELK by (destruct (Z.eqb_spec shv 7); [lia | reflexivity]);
  pa_s_run PA_SELK; pa_keep pa_s_kwr; pa_s_leaf HR0
| replace (if shv =? 7 then PA_SEL7 else PA_SELK) with PA_SEL7 by (destruct (Z.eqb_spec shv 7); [reflexivity | lia]);
  pa_s_run PA_SEL7; pa_keep pa_s_kwr; pa_s_leaf HR0 ]
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Notation pa_post := (rts_post B MT).

(* the goal of the block, for both entry states *)
Definition pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i sh plen nl cur b : Z) : Prop :=
SRr rsegs W (cfg_at rsegs PA_N regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if sh =? 7 then PA_SEL7 else PA_SELK)
 [10; 11; 12; 13; 14; 24]%bv
 (fun a => R + 0xf8 <= a < R + 0x100 \/ R + 0x100 <= a < R + 0x108)
 (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 plen /\ getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 12 = w64 (plen - 0x3ffd) /\ getr regs2 24 = w64 (if nl =? 0 then 0 else nl - 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf8) 8 i /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x100) 8 (if nl =? 0 then cur else cur + 1))).

(* nl > 0: the byte at the cursor is read *)
Lemma pa_s_sel1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 16 = w64 i -> getr regs 27 = w64 pp -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 nl ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 < nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
amem_range cur 1 -> ~ (R + 0xd8 <= cur < R + 0x108) -> ~ (R + 0x130 <= cur < R + 0x138) ->
~ (pp <= cur < pp + Layout.PP_SIZE) ->
pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i sh plen nl cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
  HJ H9 H16 H27 H23 H22 H18 H24 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vcur Vplen Hplen Hi Hnl Hcur0 Hcurn
  Vb Hb HRAc Hamr HnR1 HnR2 Hnpp.
unfold pa_s_goal.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HRlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppceil, Hppapp. unfold Layout.PP_SIZE in Hnpp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hppapp.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
destruct (rtm_ra_cell _ _ _ HRAc) as (s & Hs & Hsok).
destruct (rtm_aview_val1 rsegs _ _ _ _ Hs) as (_ & Hs256).
assert (Hs8 : 0 <= s < 8) by (destruct Hsok as [-> | [_ Hs8]]; lia).
set (sa := shadow_of_addr SHADOW_OFF cur) in Hs.
assert (Hsa : sa = 0x7fff8000 + cur / 8) by reflexivity.
pose proof (pa_s_div8 cur ltac:(lia)) as Hcur8. pose proof (pa_s_div8 (pp + 0x4000) ltac:(lia)) as Hpp8.
set (E := Ereg regs (pa_extra [nl; cur; sh; plen; b; sa; s])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E27 : bv_unsigned (ew E 27) = pp) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; unfold w64; apply unsigned_lit_small; lia).
assert (W27 : ew E 27 = Z_to_bv 64 pp) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (W16 : ew E 16 = Z_to_bv 64 i) by (unfold E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl), H16; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 nl) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 cur) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 sh) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 plen) by reflexivity.
assert (E37 : ew E 37 = Z_to_bv 64 b) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 sa) by reflexivity.
assert (E39 : ew E 39 = Z_to_bv 64 s) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
(* the entry registers *)
assert (D24 : sv_denot E (SOff 33 0) = getr regs 24).
{ rewrite H24. unfold w64. rewrite (pa_s_doff E 33 nl 0 E33) by lia. rewrite Z.add_0_r. reflexivity. }
assert (HR0 : regs_ok E (pa_s_sr (SOff 33 0)) regs) by (exact (pa_s_regs_ok regs _ pp _ H27 ltac:(lia) H23 H22 H18 D24)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s1 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (rtm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vsh].
    + apply (rtm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia | constructor].
    + apply (rtm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E34 | lia] | lia | rewrite Z.add_0_r; exact Vcur].
    + apply (rtm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. apply (pa_chunk8 _ _ _ _ _ (2 ^ 64 - 0x3ffd)); [| lia | exact Ve8].
      cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    + apply (rtm_ro_region rsegs E _ _ 27 pp); [exact E27 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E36 | lia] | lia | rewrite Z.add_0_r; exact Vplen].
    + apply (rtm_cell_region rsegs E _ _ 34 cur b); [rewrite E34; apply unsigned_lit_small; lia | | | lia | lia].
      * apply (rtm_val1_aview rsegs); assumption.
      * rewrite (pa_s_doff E 37 b 0 E37) by lia. rewrite Z.add_0_r. reflexivity.
    + apply (rtm_cell_region rsegs E _ _ 38 sa s); [rewrite E38; apply unsigned_lit_small; lia | exact Hs | | lia | lia].
      rewrite (pa_s_doff E 39 s 0 E39) by lia. rewrite Z.add_0_r. reflexivity.
  - unfold pa_s_rd8, pa_s_rf8, pa_s_r100, pa_s_r130, pa_s_rlen, pa_s_rin, pa_s_rcell.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite !E9, !E27, E34, E38, !unsigned_lit_small by lia.
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [pa_s_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, E33, E34, E35, E36, E37, E39, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; lia.
    + cbn [pa_s_G1 f_alias alias_ok]. split; [|exact I].
      assert (U34 : U E (SOff 34 0) = cur) by (rewrite (pa_s_Uoff E 34 cur 0 E34) by lia; apply Z.add_0_r).
      assert (Hlt : U E (SOff 32 0) + U E (SOff 34 0) / 8 < 2 ^ 64) by (rewrite U32, U34; unfold SHADOW_OFF; lia).
      rewrite (pa_s_den E _ sa); [rewrite (pa_s_den E (SOff 38 0) sa); [reflexivity |] |].
      * rewrite (pa_s_Uoff E 38 sa 0 E38) by lia. apply Z.add_0_r.
      * rewrite (pa_s_shU E _ _ Hlt), U32, U34. exact (eq_sym Hsa). }
clearbody E.
assert (SHOK : sh_ok rsegs PABx pa_s_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, pa_s_SH. constructor; [|constructor].
  eapply (shent_ok_of_block rsegs B LAWS); [exact HAR | exact Hpp | exact U32 | | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
  rewrite (pa_s_Uoff E 27 pp 0 W27) by lia. apply Z.add_0_r. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100 \/ R + 0x100 <= a < R + 0x108) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
assert (Hnz : (nl =? 0) = false) by (apply Z.eqb_neq; lia). rewrite !Hnz.
unfold cfg_at. change (w64 PA_N) with (Z_to_bv 64 PA_N).
(* 0x80e10 .. 0x80e24: stop at the beqz 0x80e28 on the cursor's shadow byte s *)
pa_s_runb. pa_keep pa_s_kwr.
pa_branch Hc; rewrite branch_eq_U, (pa_s_Uoff _ 39 _ 0 E39), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
rewrite Z.add_0_r in Hc;
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- (* s = 0: 0x80e30 .. 0x80e64, stop at the bne 0x80e68 *)
  pa_s_runb. pa_keep pa_s_kwr.
  pa_s_fin E35 HR0; pa_s_rel1 E9 W16 E33 E34 E36 E37.
- (* s <> 0: 0x80e2c j 0x82540, andi a1,a0,7; stop at the bge 0x82544 *)
  pa_s_runb. pa_keep pa_s_kwr.
  pa_branch Hg.
  + (* the report arm: cur mod 8 >= s contradicts saddr_ok *)
    exfalso.
    assert (G : sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
    { cbn [sv_denot]. rewrite E34, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    rewrite G, (pa_s_doff E 39 s 0 E39), Z.add_0_r in Hg by lia.
    cbn [branch_taken] in Hg. rewrite (rtm_ra_slow_bv cur s Hsok Hc) in Hg. cbn in Hg. discriminate Hg.
  + (* 0x82548 j 0x80e30 .. 0x80e64, stop at the bne 0x80e68 *)
    pa_s_runb. pa_keep pa_s_kwr.
    pa_s_fin E35 HR0; pa_s_rel1 E9 W16 E33 E34 E36 E37.
Qed.

(* nl = 0: no input is left; a1 = 0 and nothing but i is stored *)
Lemma pa_s_sel0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 16 = w64 i -> getr regs 27 = w64 pp -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 0 ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 < cur -> cur <= 2 ^ 63 ->
pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i sh plen 0 cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen cur b
  HJ H9 H16 H27 H23 H22 H18 H24 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vcur Vplen Hplen Hi Hcur0 Hcurn.
unfold pa_s_goal. rewrite !Z.eqb_refl.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HRlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppceil, Hppapp.
set (E := Ereg regs (pa_extra [0; cur; sh; plen])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E27 : bv_unsigned (ew E 27) = pp) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; unfold w64; apply unsigned_lit_small; lia).
assert (W27 : ew E 27 = Z_to_bv 64 pp) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (W16 : ew E 16 = Z_to_bv 64 i) by (unfold E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl), H16; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 cur) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 sh) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 plen) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
assert (D24 : sv_denot E (SLit 0) = getr regs 24) by (rewrite H24; reflexivity).
assert (HR0 : regs_ok E (pa_s_sr (SLit 0)) regs) by (exact (pa_s_regs_ok regs _ pp _ H27 ltac:(lia) H23 H22 H18 D24)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s0 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (rtm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vsh].
    + apply (rtm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia | constructor].
    + apply (rtm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E34 | lia] | lia | rewrite Z.add_0_r; exact Vcur].
    + apply (rtm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. apply (pa_chunk8 _ _ _ _ _ (2 ^ 64 - 0x3ffd)); [| lia | exact Ve8].
      cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    + apply (rtm_ro_region rsegs E _ _ 27 pp); [exact E27 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E36 | lia] | lia | rewrite Z.add_0_r; exact Vplen].
  - unfold pa_s_rd8, pa_s_rf8, pa_s_r100, pa_s_r130, pa_s_rlen.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite !E9, !E27.
    repeat split; lia.
  - split; [|split; exact I].
    cbn [pa_s_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E27, E32, E35, E36, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; lia. }
clearbody E.
assert (SHOK : sh_ok rsegs PABx pa_s_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, pa_s_SH. constructor; [|constructor].
  eapply (shent_ok_of_block rsegs B LAWS); [exact HAR | exact Hpp | exact U32 | | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
  rewrite (pa_s_Uoff E 27 pp 0 W27) by lia. apply Z.add_0_r. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100 \/ R + 0x100 <= a < R + 0x108) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 PA_N) with (Z_to_bv 64 PA_N).
(* 0x80e10 .. 0x80e64 (the beqz 0x80e14 taken: 0x80e44 a1 = 0), stop at the bne 0x80e68 *)
pa_s_runb. pa_keep pa_s_kwr.
pa_s_fin E35 HR0; pa_s_rel0 E9 W16 E34 E36.
Qed.

(* ---- the sel block 0x80e10 -> SEL7 0x80e6c (sh = 7) / SELK 0x81018 ---- *)
Lemma pa_sel : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 16 = w64 i -> getr regs 27 = w64 pp -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 nl ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
(0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ 0 <= b < 256 /\
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 /\
  amem_range cur 1 /\ ~ (R + 0xd8 <= cur < R + 0x108) /\ ~ (R + 0x130 <= cur < R + 0x138) /\
  ~ (pp <= cur < pp + Layout.PP_SIZE)) ->
SRr rsegs W (cfg_at rsegs PA_N regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if sh =? 7 then PA_SEL7 else PA_SELK)
 [10; 11; 12; 13; 14; 24]%bv
 (fun a => R + 0xf8 <= a < R + 0x100 \/ R + 0x100 <= a < R + 0x108)
 (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 plen /\ getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 12 = w64 (plen - 0x3ffd) /\ getr regs2 24 = w64 (if nl =? 0 then 0 else nl - 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf8) 8 i /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x100) 8 (if nl =? 0 then cur else cur + 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
  HJ H9 H16 H27 H23 H22 H18 H24 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vcur Vplen Hplen Hi Hnl Hcur0 Hcurn Hin.
destruct (Z.eq_dec nl 0) as [-> | Hnz].
- exact (pa_s_sel0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen cur b
    HJ H9 H16 H27 H23 H22 H18 H24 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vcur Vplen Hplen Hi Hcur0 ltac:(lia)).
- destruct (Hin ltac:(lia)) as (Vb & Hb & HRAc & Hamr & HnR1 & HnR2 & Hnpp).
  exact (pa_s_sel1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
    HJ H9 H16 H27 H23 H22 H18 H24 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vcur Vplen Hplen Hi ltac:(lia) Hcur0 Hcurn
    Vb Hb HRAc Hamr HnR1 HnR2 Hnpp).
Qed.

End d.
End c.

(* ================================ the selector piece: N -> SEL7 / SELK ================================ *)
Section ps. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma pa_piece_sel : rs_piece_W4_sel_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_sel_stmt. intros cx POST rest i Hst HS7 HSK.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
assert (PA' : q_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= q_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rs_from_N. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
assert (Ppin2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
pose proof Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : rs_cur rsegs cx rest r = q_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Lr; lia).
assert (Hsh8 : 0 <= sh < 8) by (exact (proj1 Hwf)).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (q_R (x_e cx)) A9. pa_take Hat (LReg 16) (Z.of_nat (length ps)) A16.
pa_take Hat (LReg 27) (q_pp (x_e cx)) A27.
pa_take Hat (LReg 23) (q_pp (x_e cx) + 0x4000) A23. pa_take Hat (LReg 22) (shadow_addr (q_pp (x_e cx) + 0x4000)) A22.
pa_take Hat (LReg 18) SHADOW_OFF A18. pa_take Hat (LReg 24) (Z.of_nat (length r)) A24.
pa_take Hat (LCell XR 0xd8) sh Ad8. pa_take Hat (LCell XR 0x130) (-0x3ffd) A130.
pa_take Hat (LCell XR 0x100) (rs_cur rsegs cx rest r) A100.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity. rewrite M2 in A130.
rewrite Z.mod_small in Ad8 by lia.
rewrite Z.mod_small in A100 by (rewrite Hcur; lia).
assert (Hplen : rs_plen sh ps = Z.of_nat (length (pc_buf (PbCut sh ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rs_plen sh ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rtm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
assert (Hinp : 0 < Z.of_nat (length r) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (rs_cur rsegs cx rest r) 1 (fst (fuzz_u8 r)) /\ 0 <= fst (fuzz_u8 r) < 256 /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rs_cur rsegs cx rest r) 1 /\
  amem_range (rs_cur rsegs cx rest r) 1 /\
  ~ (q_R (x_e cx) + 0xd8 <= rs_cur rsegs cx rest r < q_R (x_e cx) + 0x108) /\
  ~ (q_R (x_e cx) + 0x130 <= rs_cur rsegs cx rest r < q_R (x_e cx) + 0x138) /\
  ~ (q_pp (x_e cx) <= rs_cur rsegs cx rest r < q_pp (x_e cx) + Layout.PP_SIZE)).
{ intros Hnz. rewrite Hcur. destruct r as [|bb r''] eqn:Er'; [cbn in Hnz; lia|]. cbn [fuzz_u8 fst].
  destruct (pa_nth_skipn rest j bb r'' (eq_sym Er)) as (Hjl & Hnth).
  destruct (pa_input_now B MT LAWS cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) Hpre Hfsh0 Hin Hcore Hfsh ltac:(lia))
    as (V & RA).
  assert (Hb : nth (Z.to_nat (Z.of_nat j)) (rs_u8s rest) 0 = bv_unsigned bb).
  { rewrite Nat2Z.id. unfold rs_u8s. rewrite (nth_indep _ _ ((fun x : byte => bv_unsigned x) (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth, Hnth. reflexivity. }
  rewrite Hb in V. destruct (Hapart (q_src (x_e cx) + Z.of_nat j) ltac:(lia)) as (N1 & N2 & N3).
  split; [exact V|]. split; [pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia|].
  split; [exact RA|]. split; [unfold amem_range in *; lia|]. split; [|split; [|exact N3]].
  - intros X. apply N2. unfold rt_inw. cbn [hi_w1 rate_himg_A].
    apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
  - intros X. apply N2. unfold rt_inw. cbn [hi_w1 rate_himg_A].
    apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
    cbn [fst snd rt_xv]. lia. }
eapply SRr_bind.
{ refine (pa_sel B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (q_pp (x_e cx)) (Z.of_nat (length ps)) sh
    (rs_plen sh ps) (Z.of_nat (length r)) (rs_cur rsegs cx rest r) (fst (fuzz_u8 r))
    HJ A9 A16 A27 A23 A22 A18 A24 RB1 RB2 RB3 Ppin2 Ad8 Hsh8 A130 A100 Alen _ _ _ _ _ Hinp); rewrite ?Hplen, ?Hcur; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R10 & R11 & R12 & R24 & Vf8 & V100).
set (R := q_R (x_e cx)) in *. set (pp := q_pp (x_e cx)) in *. set (F := q_F (x_e cx)) in *.
(* the cursor after the selector byte *)
assert (Hstep : getr regs3 11 = w64 (fst (fuzz_u8 r)) /\
  getr regs3 24 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))) /\
  val_mem rsegs (mrestrict (w_H W3) mem3) (R + 0x100) 8 (rs_cur rsegs cx rest (snd (fuzz_u8 r)) mod 2 ^ 64)).
{ rewrite Hcur in V100. destruct r as [|bb r''] eqn:Er'.
  - cbn [fuzz_u8 fst snd length Z.of_nat Z.eqb] in R11, R24, V100 |- *.
    rewrite Hcur, Z.mod_small by lia. split; [exact R11|]. split; [exact R24 | exact V100].
  - cbn [fuzz_u8 fst snd length] in R11, R24, V100 |- *.
    replace (Z.of_nat (S (length r'')) =? 0) with false in R11, R24, V100 by (symmetry; apply Z.eqb_neq; lia).
    unfold rs_cur. cbn [length] in Lr. rewrite Z.mod_small by lia.
    split; [exact R11|]. split.
    + replace (Z.of_nat (length r'')) with (Z.of_nat (S (length r'')) - 1) by lia. exact R24.
    + replace (q_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r'')) with (q_src (x_e cx) + Z.of_nat j + 1) by lia.
      exact V100. }
destruct Hstep as (R11' & R24' & V100').
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. right. apply pa_E1_R. fold R. lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. intros jj Hjj.
  replace (Z.of_nat (length rs_P0)) with 56 in Hjj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold shadow_addr, SHADOW_OFF. apply Hmem; [lia|]. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ unfold rs_pp_at in *. eapply (rtm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 16384) by lia.
  unfold pc_image in Hx. rewrite (length_pp_image _ _ _ _ _ _ Hb16 IB3 IB4) in Hx. fold pp in Hx.
  apply Hmem; unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 26, -0x4001); (LReg 22, shadow_addr (pp + 0x4000)); (LReg 25, rs_seen ps)]
   ++ rs_Kc rsegs cx sh np ++ rs_Hc rsegs cx)).
{ eapply pa_at_move; [pa_list; pa_from Hat|].
  cbn [rs_L_N rs_L_SEL rs_L_KEY rs_L_P rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rt_xv].
  all: try (apply Hkeep; [cbv; discriminate | pa_notin]).
  all: let jj := fresh "jj" in let Hjj := fresh "Hjj" in intros jj Hjj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (HatS : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_SEL rsegs cx sh np ps rest (snd (fuzz_u8 r)))).
{ pa_list; first [pa_from Hat3 | idtac].
  - cbn [rt_at]. exact (eq_trans R10 eq_refl).
  - cbn [rt_at]. exact (eq_trans R12 eq_refl).
  - cbn [rt_at rt_xv]. fold R. rewrite Z.mod_small by lia. exact Vf8.
  - cbn [rt_at rt_xv]. fold R. exact V100'.
  - cbn [rt_at]. exact R24'. }
assert (Hbase : forall sh', sh' = sh -> rs_prop_base rsegs B MT cx sh' np ps rest (snd (fuzz_u8 r)) ly3 S3 W3 regs3 mem3 md3).
{ intros sh' ->. split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|].
  split; [apply pa_suffix_step; exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
  split; [rewrite <- Hloop; reflexivity|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hps | exact Hnp3]. }
destruct (Z.eqb_spec sh 7) as [E7|E7].
- change (mkCfg (mkst regs3 (w64 PA_SEL7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SEL7 regs3 mem3 md3).
  apply (HS7 ly3 S3 W3 regs3 mem3 md3 np ps (snd (fuzz_u8 r)) Hlen).
  rewrite E7 in HatS, Hpp3.
  split; [exact (Hbase 7 (eq_sym E7))|]. split; [exact HatS|]. split; [exact Hpp3|].
  rewrite <- E7, <- Hloop. reflexivity.
- change (mkCfg (mkst regs3 (w64 PA_SELK) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_SELK regs3 mem3 md3).
  apply (HSK ly3 S3 W3 regs3 mem3 md3 sh np (fst (fuzz_u8 r)) ps (snd (fuzz_u8 r)) Hlen).
  split; [exact (Hbase sh eq_refl)|]. split.
  + unfold rs_at_cx. apply pa_at_app; [exact HatS|]. constructor; [|constructor]. cbn [rt_at fst snd]. exact R11'.
  + split; [exact Hpp3|]. split; [exact E7|].
    split; [destruct r as [|bb r'']; cbn [fuzz_u8 fst]; [lia | pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia]|].
    rewrite <- Hloop. cbn [snd]. destruct (fuzz_u8 r); reflexivity.
Qed.
End ps.

Print Assumptions pa_piece_sel.
