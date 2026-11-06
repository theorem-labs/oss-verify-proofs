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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheckList.v, with its module paths and module names changed; 378 of its 448 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSelB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); the input cursor is the register s11 (atom 27), not the cell R+0xc8, so pp gets its own env slot (34) and the cursor's region, alias fact and relation move to atom 27; the property index is in a7 (role a6); the cells move by the plan's slot map (R+0x98 -> R+0xb8, R+0xb8 -> R+0xd8, R+0xe8 -> R+0x108, R+0xf8 -> R+0x118); module paths. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on its unstripped
   twin sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the sel block N 0x812f4 of
   LLVMFuzzerTestOneInput's property loop, to SEL7 0x81358 (sh = 7) or SELK 0x81514, as a block lemma over
   lib/A/HPgPropKit.v. Proves no function (kind: segment lemma).
     0x812f4 sd a7,0xd8(s1)                      i
     0x812f8 ld a0,0x118(s1); 0x812fc beqz a0    no input left: 0x8132c sd zero,0x118(s1); a1 = 0; -> 0x81334
     0x81300 srli a0,s11,3 .. 0x81310            the check of the byte at the cursor s11 (EQ-J: add a0,a0,s7;
                                                 lb a0,0(a0); beqz a0,+8; j 0x82ad8 = andi a1,s11,7;
                                                 bge a1,a0,+8 (-> 0x82ae4, the report); j 0x81314)
     0x81314 lbu a1,0(s11); s11 + 1; R+0x118 - 1 and its store; j 0x81334
     0x81334 the check of pp->len (lbu a0,0(s4); beqz a0,+8); 0x81340 ld a0,0(s5) = len; a2 = len + R+0x108
     (= len - 0x3ffd); 0x8134c ld a3,0xb8(s1) = sh; a4 = 7; 0x81354 bne a3,a4 -> 0x81514, else 0x81358.
   The walk splits on nl = 0 before its entry state. With nl > 0 the input byte b is a region based at the cursor's
   atom 27 and its shadow byte s a region based at a fresh atom (the cursor's shadow address, tied to the cursor by an
   alias fact); s = 0 runs on, s <> 0 goes through 0x82ad8, whose report arm dies by saddr_ok. pp is in no register
   here: it is env slot 34, s5 = pp + 0x4000 and s4 = its shadow address; pp's len cell is a region based at atom 34,
   and the shadow entry of the whole pp block makes the check of pp->len free. The two stores are the write windows
   of two 8-byte regions based at atom 9 (R). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgSteps HPgMem HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry states ----
   atom 27 is s11, the cursor cur; env slots (pa_extra): 32 K, 33 nl, 34 pp, 35 sh, 36 plen, 37 b, 38 the cursor's
   shadow address, 39 its byte s *)
Definition pa_s_SH : list shent := [mkSHE 34 0 19744].
(* s4 = the shadow address of pp + 0x4000, s5 = pp + 0x4000, s7 = K *)
Definition pa_s_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms (20%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0x4000) (SLit 3)) (SOff 32 0)))
    (21%bv : bv 5) (SOff 34 0x4000)) (23%bv : bv 5) (SOff 32 0).
(* the four cells of R the block reads or writes (each write window exactly its 8 bytes) and pp's len cell *)
Definition pa_s_rb8 : YP09.region := YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0 0 [ YP09.mkChunk 0xb8 (CVal 8 (SOff 35 0)) ].
Definition pa_s_rd8 : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xe0 0xd8 0xe0 [].
Definition pa_s_r108 : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [ YP09.mkChunk 0x108 (CVal 8 (SLit (-16381))) ].
Definition pa_s_r118 (nlv : sv) : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x120 0x118 0x120 [ YP09.mkChunk 0x118 (CVal 8 nlv) ].
Definition pa_s_rlen : YP09.region := YP09.mkRegion (Some 34%nat) 0x4000 0x4008 0 0 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 36 0)) ].
(* the input byte at the cursor and its shadow byte *)
Definition pa_s_rin : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 37 0)) ].
Definition pa_s_rcell : YP09.region := YP09.mkRegion (Some 38%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 39 0)) ].
(* R lies in the stack above the allocator's ceiling; pp's upper bound keeps the shadow of its block in the span *)
Definition pa_s_G1 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 1 9223372036854775807 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (33%nat, mkAF 1 9223372036854775807 0); (34%nat, mkAF 4096 140737479946976 4); (35%nat, mkAF 0 7 0);
    (36%nat, mkAF 0 5440 0); (37%nat, mkAF 0 255 0); (39%nat, mkAF 0 7 0) ] []
  [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0) (SLit 3)) (SOff 32 0), SOff 38 0) ].
Definition pa_s_G0 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (34%nat, mkAF 4096 140737479946976 4);
    (35%nat, mkAF 0 7 0); (36%nat, mkAF 0 5440 0) ] [] [].
Definition ss_s1 : sstate :=
  mkSS PA_N pa_s_sr [pa_s_rb8; pa_s_rd8; pa_s_r108; pa_s_r118 (SOff 33 0); pa_s_rlen; pa_s_rin; pa_s_rcell] None pa_s_G1.
Definition ss_s0 : sstate :=
  mkSS PA_N pa_s_sr [pa_s_rb8; pa_s_rd8; pa_s_r108; pa_s_r118 (SLit 0); pa_s_rlen] None pa_s_G0.

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
(* the entry registers: sr_atoms with s4, s5 and s7 as the shadow address of pp + 0x4000, pp + 0x4000 and K
   (pp is env slot 34) *)
Lemma pa_s_regs_ok : forall regs nl pp rest, 0 <= pp < 2 ^ 47 ->
getr regs 21 = w64 (pp + 0x4000) -> getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
regs_ok (Ereg regs (pa_extra (nl :: pp :: rest))) pa_s_sr regs.
Proof.
intros regs nl pp rest Hpp H21 H20 H23. set (E := Ereg regs (pa_extra (nl :: pp :: rest))).
assert (W34 : ew E 34 = Z_to_bv 64 pp) by reflexivity.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
unfold pa_s_sr. apply pa_s_override; [apply pa_s_override; [apply pa_s_override; [apply regs_ok_Ereg | | ] | | ] | | ].
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H20. unfold w64, shadow_addr. apply pa_s_den.
  assert (U34 : U E (SOff 34 0x4000) = pp + 0x4000) by (apply (pa_s_Uoff E 34 pp 0x4000 W34); lia).
  pose proof (pa_s_div8 (pp + 0x4000) ltac:(lia)) as Hpp8.
  assert (Hlt : U E (SOff 32 0) + U E (SOff 34 0x4000) / 8 < 2 ^ 64) by (rewrite U32, U34; unfold SHADOW_OFF; lia).
  rewrite (pa_s_shU E _ _ Hlt), U32, U34. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H21. unfold w64. apply pa_s_doff; [exact W34 | lia].
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H23. unfold w64. rewrite (pa_s_doff E 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia).
  rewrite Z.add_0_r. reflexivity.
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
(* the leaf: pa_post's first eight clauses (HPgPropKit's pa_leaf, with the registers kept against the entry's
   symbolic registers HR0, which override s4, s5 and s7); the relation is left *)
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
(* the relation at the end, nl > 0: a0 = plen, a1 = b, a2 = plen - 0x3ffd; R+0xd8 = i, s11 = cur + 1,
   R+0x118 = nl - 1 (regions 1 and 3 of the end state) *)
Ltac pa_s_rel1 E9 W17 W27 E33 E36 E37 :=
lazymatch type of E9 with bv_unsigned _ = ?Rv =>
cbv beta;
pa_reg (10%bv : bv 5); pa_reg (11%bv : bv 5); pa_reg (12%bv : bv 5); pa_reg (27%bv : bv 5);
refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
[ unfold w64; rewrite (pa_s_doff _ 36 _ 0 E36) by lia; rewrite Z.add_0_r; reflexivity
| unfold w64; rewrite (pa_s_doff _ 37 _ 0 E37) by lia; rewrite Z.add_0_r; reflexivity
| unfold w64; rewrite (pa_s_doff _ 36 _ (-16381) E36) by lia; reflexivity
| pa_s_val 1%nat Rv 0xd8; [exact E9 | rewrite (pa_s_doff _ 17 _ 0 W17) by lia; rewrite Z.add_0_r; reflexivity | lia]
| unfold w64; rewrite (pa_s_doff _ 27 _ 1 W27) by lia; reflexivity
| pa_s_val 3%nat Rv 0x118; [exact E9 | rewrite (pa_s_doff _ 33 _ (-1) E33) by lia; reflexivity | lia] ]
end.
(* the relation at the end, nl = 0: a1 = 0, s11 = cur (not written), R+0x118 = 0 *)
Ltac pa_s_rel0 E9 W17 W27 E36 :=
lazymatch type of E9 with bv_unsigned _ = ?Rv =>
cbv beta;
pa_reg (10%bv : bv 5); pa_reg (11%bv : bv 5); pa_reg (12%bv : bv 5); pa_reg (27%bv : bv 5);
refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
[ unfold w64; rewrite (pa_s_doff _ 36 _ 0 E36) by lia; rewrite Z.add_0_r; reflexivity
| reflexivity
| unfold w64; rewrite (pa_s_doff _ 36 _ (-16381) E36) by lia; reflexivity
| pa_s_val 1%nat Rv 0xd8; [exact E9 | rewrite (pa_s_doff _ 17 _ 0 W17) by lia; rewrite Z.add_0_r; reflexivity | lia]
| unfold w64; rewrite (pa_s_doff _ 27 _ 0 W27) by lia; rewrite Z.add_0_r; reflexivity
| pa_s_val 3%nat Rv 0x118; [exact E9 | reflexivity | lia] ]
end.
(* 0x81354 bne a3,a4 (sh against 7): taken -> SELK 0x81514, else SEL7 0x81358; run to the target, leaf; the
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
Local Notation pa_post := (pa_post B MT).

(* the goal of the block, for both entry states *)
Definition pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i sh plen nl cur b : Z) : Prop :=
SRr rsegs W (cfg_at rsegs PA_N regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if sh =? 7 then PA_SEL7 else PA_SELK)
 [10; 11; 12; 13; 14; 27]%bv
 (fun a => R + 0xd8 <= a < R + 0xe0 \/ R + 0x118 <= a < R + 0x120)
 (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 plen /\ getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 12 = w64 (plen - 0x3ffd) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xd8) 8 i /\
   getr regs2 27 = w64 (if nl =? 0 then cur else cur + 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 (if nl =? 0 then 0 else nl - 1))).

(* nl > 0: the byte at the cursor is read *)
Lemma pa_s_sel1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 17 = w64 i -> getr regs 27 = w64 cur -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 nl ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 < nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
amem_range cur 1 -> ~ (R <= cur < R + 0x160) -> ~ (pp <= cur < pp + Layout.PP_SIZE) ->
pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i sh plen nl cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
  HJ H9 H17 H27 H21 H20 H23 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vnl Vplen Hplen Hi Hnl Hcur0 Hcurn
  Vb Hb HRAc Hamr HnR Hnpp.
unfold pa_s_goal.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HRlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppceil, Hppapp. unfold Layout.PP_SIZE in Hnpp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hppapp.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
destruct (hm_ra_cell _ _ _ HRAc) as (s & Hs & Hsok).
destruct (hm_aview_val1 rsegs _ _ _ _ Hs) as (_ & Hs256).
assert (Hs8 : 0 <= s < 8) by (destruct Hsok as [-> | [_ Hs8]]; lia).
set (sa := shadow_of_addr SHADOW_OFF cur) in Hs.
assert (Hsa : sa = 0x7fff8000 + cur / 8) by reflexivity.
pose proof (pa_s_div8 cur ltac:(lia)) as Hcur8. pose proof (pa_s_div8 (pp + 0x4000) ltac:(lia)) as Hpp8.
set (E := Ereg regs (pa_extra [nl; pp; sh; plen; b; sa; s])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E27 : bv_unsigned (ew E 27) = cur) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; unfold w64; apply unsigned_lit_small; lia).
assert (W27 : ew E 27 = Z_to_bv 64 cur) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (W17 : ew E 17 = Z_to_bv 64 i) by (unfold E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 nl) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 pp) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 sh) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 plen) by reflexivity.
assert (E37 : ew E 37 = Z_to_bv 64 b) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 sa) by reflexivity.
assert (E39 : ew E 39 = Z_to_bv 64 s) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
(* the entry registers *)
assert (HR0 : regs_ok E pa_s_sr regs) by (exact (pa_s_regs_ok regs nl pp _ ltac:(lia) H21 H20 H23)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s1 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vsh].
    + apply (hm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia | constructor].
    + apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. apply (pa_chunk8 _ _ _ _ _ (2 ^ 64 - 0x3ffd)); [| lia | exact Ve8].
      cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    + apply (hm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E33 | lia] | lia | rewrite Z.add_0_r; exact Vnl].
    + apply (hm_ro_region rsegs E _ _ 34 pp); [rewrite E34; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E36 | lia] | lia | rewrite Z.add_0_r; exact Vplen].
    + apply (hm_cell_region rsegs E _ _ 27 cur b); [exact E27 | | | lia | lia].
      * apply (hm_val1_aview rsegs); assumption.
      * rewrite (pa_s_doff E 37 b 0 E37) by lia. rewrite Z.add_0_r. reflexivity.
    + apply (hm_cell_region rsegs E _ _ 38 sa s); [rewrite E38; apply unsigned_lit_small; lia | exact Hs | | lia | lia].
      rewrite (pa_s_doff E 39 s 0 E39) by lia. rewrite Z.add_0_r. reflexivity.
  - unfold pa_s_rb8, pa_s_rd8, pa_s_r108, pa_s_r118, pa_s_rlen, pa_s_rin, pa_s_rcell.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite !E9, !E27, !E34, !E38, !unsigned_lit_small by lia.
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [pa_s_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, E33, E34, E35, E36, E37, E39, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; lia.
    + cbn [pa_s_G1 f_alias alias_ok]. split; [|exact I].
      assert (U27 : U E (SOff 27 0) = cur) by (rewrite (pa_s_Uoff E 27 cur 0 W27) by lia; apply Z.add_0_r).
      assert (Hlt : U E (SOff 32 0) + U E (SOff 27 0) / 8 < 2 ^ 64) by (rewrite U32, U27; unfold SHADOW_OFF; lia).
      rewrite (pa_s_den E _ sa); [rewrite (pa_s_den E (SOff 38 0) sa); [reflexivity |] |].
      * rewrite (pa_s_Uoff E 38 sa 0 E38) by lia. apply Z.add_0_r.
      * rewrite (pa_s_shU E _ _ Hlt), U32, U27. exact (eq_sym Hsa). }
clearbody E.
assert (SHOK : sh_ok rsegs PABx pa_s_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, pa_s_SH. constructor; [|constructor].
  eapply (shent_ok_of_block rsegs B LAWS); [exact HAR | exact Hpp | exact U32 | | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
  rewrite (pa_s_Uoff E 34 pp 0 E34) by lia. apply Z.add_0_r. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xd8 <= a < R + 0xe0 \/ R + 0x118 <= a < R + 0x120) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
assert (Hnz : (nl =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Hnz.
unfold cfg_at. change (w64 PA_N) with (Z_to_bv 64 PA_N).
(* 0x812f4 .. 0x81308: stop at the beqz 0x8130c on the cursor's shadow byte s *)
pa_s_runb. pa_keep pa_s_kwr.
pa_branch Hc; rewrite branch_eq_U, (pa_s_Uoff _ 39 _ 0 E39), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
rewrite Z.add_0_r in Hc;
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- (* s = 0: 0x81314 .. 0x81350, stop at the bne 0x81354 *)
  pa_s_runb. pa_keep pa_s_kwr.
  pa_s_fin E35 HR0; pa_s_rel1 E9 W17 W27 E33 E36 E37.
- (* s <> 0: 0x81310 j 0x82ad8, andi a1,s11,7; stop at the bge 0x82adc *)
  pa_s_runb. pa_keep pa_s_kwr.
  pa_branch Hg.
  + (* the report arm (0x82ae4): cur mod 8 >= s contradicts saddr_ok *)
    exfalso.
    assert (G : sv_denot E (SAlu ALU_AND (SOff 27 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
    { cbn [sv_denot]. rewrite W27, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    rewrite G, (pa_s_doff E 39 s 0 E39), Z.add_0_r in Hg by lia.
    cbn [branch_taken] in Hg. rewrite (hm_ra_slow_bv cur s Hsok Hc) in Hg. cbn in Hg. discriminate Hg.
  + (* 0x82ae0 j 0x81314 .. 0x81350, stop at the bne 0x81354 *)
    pa_s_runb. pa_keep pa_s_kwr.
    pa_s_fin E35 HR0; pa_s_rel1 E9 W17 W27 E33 E36 E37.
Qed.

(* nl = 0: no input is left; R+0x118 gets 0 and a1 = 0 *)
Lemma pa_s_sel0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 17 = w64 i -> getr regs 27 = w64 cur -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 < cur -> cur <= 2 ^ 63 ->
pa_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i sh plen 0 cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen cur b
  HJ H9 H17 H27 H21 H20 H23 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vnl Vplen Hplen Hi Hcur0 Hcurn.
unfold pa_s_goal. rewrite Z.eqb_refl.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HRlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppceil, Hppapp.
set (E := Ereg regs (pa_extra [0; pp; sh; plen])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (W27 : ew E 27 = Z_to_bv 64 cur) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (W17 : ew E 17 = Z_to_bv 64 i) by (unfold E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 pp) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 sh) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 plen) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pa_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
assert (HR0 : regs_ok E pa_s_sr regs) by (exact (pa_s_regs_ok regs 0 pp _ ltac:(lia) H21 H20 H23)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s0 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vsh].
    + apply (hm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia | constructor].
    + apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. apply (pa_chunk8 _ _ _ _ _ (2 ^ 64 - 0x3ffd)); [| lia | exact Ve8].
      cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    + apply (hm_rw_region rsegs E _ _ 9 R); [exact E9 | lia | lia | intros o Ho; apply Hpres; lia |].
      constructor; [|constructor]. apply (pa_chunk8 _ _ _ _ _ 0); [reflexivity | lia | exact Vnl].
    + apply (hm_ro_region rsegs E _ _ 34 pp); [rewrite E34; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. eapply pa_chunk8; [apply pa_s_doff; [exact E36 | lia] | lia | rewrite Z.add_0_r; exact Vplen].
  - unfold pa_s_rb8, pa_s_rd8, pa_s_r108, pa_s_r118, pa_s_rlen.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite !E9, !E34, !unsigned_lit_small by lia.
    repeat split; lia.
  - split; [|split; exact I].
    cbn [pa_s_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E32, E34, E35, E36, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; lia. }
clearbody E.
assert (SHOK : sh_ok rsegs PABx pa_s_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, pa_s_SH. constructor; [|constructor].
  eapply (shent_ok_of_block rsegs B LAWS); [exact HAR | exact Hpp | exact U32 | | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
  rewrite (pa_s_Uoff E 34 pp 0 E34) by lia. apply Z.add_0_r. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xd8 <= a < R + 0xe0 \/ R + 0x118 <= a < R + 0x120) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 PA_N) with (Z_to_bv 64 PA_N).
(* 0x812f4 .. 0x81350 (the beqz 0x812fc taken: 0x8132c sd zero,0x118(s1); a1 = 0), stop at the bne 0x81354 *)
pa_s_runb. pa_keep pa_s_kwr.
pa_s_fin E35 HR0; pa_s_rel0 E9 W17 W27 E36.
Qed.

(* ---- the sel block 0x812f4 -> SEL7 0x81358 (sh = 7) / SELK 0x81514 ---- *)
Lemma pa_sel : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp i sh plen nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 17 = w64 i -> getr regs 27 = w64 cur -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 sh -> 0 <= sh < 8 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 nl ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen -> 0 <= plen <= 5440 ->
0 <= i <= 2 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
(0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ 0 <= b < 256 /\
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 /\
  amem_range cur 1 /\ ~ (R <= cur < R + 0x160) /\ ~ (pp <= cur < pp + Layout.PP_SIZE)) ->
SRr rsegs W (cfg_at rsegs PA_N regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if sh =? 7 then PA_SEL7 else PA_SELK)
 [10; 11; 12; 13; 14; 27]%bv
 (fun a => R + 0xd8 <= a < R + 0xe0 \/ R + 0x118 <= a < R + 0x120)
 (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 plen /\ getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 12 = w64 (plen - 0x3ffd) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xd8) 8 i /\
   getr regs2 27 = w64 (if nl =? 0 then cur else cur + 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 (if nl =? 0 then 0 else nl - 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
  HJ H9 H17 H27 H21 H20 H23 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vnl Vplen Hplen Hi Hnl Hcur0 Hcurn Hin.
destruct (Z.eq_dec nl 0) as [-> | Hnz].
- exact (pa_s_sel0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen cur b
    HJ H9 H17 H27 H21 H20 H23 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vnl Vplen Hplen Hi Hcur0 ltac:(lia)).
- destruct (Hin ltac:(lia)) as (Vb & Hb & HRAc & Hamr & HnR & Hnpp).
  exact (pa_s_sel1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i sh plen nl cur b
    HJ H9 H17 H27 H21 H20 H23 HRlo HRhi HR16 Hpp Vsh Hsh Ve8 Vnl Vplen Hplen Hi ltac:(lia) Hcur0 Hcurn
    Vb Hb HRAc Hamr HnR Hnpp).
Qed.

End d.
End c.

Print Assumptions pa_sel.
