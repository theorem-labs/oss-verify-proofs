(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the LANE KIT of SEGMENT S5 of the ASan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput (fuzz_scene.asan, sha256
   43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026).  (rule 24: no function is proved here.) *)

(*   S5 is the cut C5 (0x82eb0) to the cut C6 (0x83020) of lib/A/P_LLVMFuzzerTestOneInput_seg.v; its walk is
   lib/A/P_LLVMFuzzerTestOneInput_S5.v (`scene_seg_S5`, which proves `seg_S5_stmt`).  This file holds the image-free
   lemmas that walk re-uses at every call site, stated over PI_scene so the asan-ubsan twin can use them unchanged.

   WHAT EACH LEMMA IS FOR.
     `s5_ch_spine`, `s5_ctx_in`  the two short lemmas P_LLVMFuzzerTestOneInput_ctx.v states as Props
                                 (rt_ch_spine_stmt, rt_ctx_in_stmt), proved here for scene.
     `s5_chain`                  cgif_file_fuzzer A/ACf5.v:172-186 `rt_chain`, image-free: the caller chain at a
                                 call of the walk, from the saved ra and s0 of `sc_saves`.
     `s5_spills_at` / `_kept`    the six spill words the block reloads -- [s1+0x18] expect, [s1+0x20] shF+0x1c,
                                 [s1+0x28] F, [s1+0x30] mac, [s1+0x38] n'', [s1+0x58] body -- and their transport
                                 across a step that keeps [sp1+24, sp1+96).
     `s5_entry`                  the block entry after a call: `pa_entry_st_ok_full` (A/Prog/ScenePaLib.v:71) over
                                 `Eimg (Ereg regs (s5_extra body nn))` and the single read-only spill region.
                                 MEASURED: the spills are s1-relative (s1 = x9), so the region's base atom is 9.
     `s5_rk` / `_pres` / `_kept` the callee-saved registers the whole block relies on: sp = s1 = sp1, s0 = sp0,
                                 gp, tp, s3 = shF, s7 = F, s8 = n'.
     `s5_seqz_xor`               `seqz s2,(s8 xor 8904)` of 0x82ec0-0x82ecc is `n' =? 8904`; this decides the
                                 0x82efc abort edge against a Theorem Labs lane's set_mac post.
     `s5_prot` / `s5_row`        the byte sets S5 hands back unchanged at C6 (spills, the 13 saved words, the frame
                                 flag word, `mac`, and the frame shadow outside the `expect` row) and the `expect`
                                 shadow row the set_shadow_00 / set_shadow_f8 pair works on. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YO0c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
(* The walk is over scene's concrete image instance PI_scene (A/Prog/SceneImg.v:56): the cut pcs of
   `scene_geom_asan` (P_LLVMFuzzerTestOneInput_seg.v) are stated over it, as is the entry file's SEGS. *)
#[local] Notation PI := PI_scene.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).

(* ---- the caller chain of the entry, and the two short lemmas the walk context states as Props ---- *)
Lemma s5_ch_spine : rt_ch_spine_stmt SEGS.
Proof. intros cx. unfold rt_ch. destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); reflexivity. Qed.
Lemma s5_ctx_in : forall RA, rt_ctx_in_stmt SEGS RA.
Proof.
intros RA cx site L Hra H1 H2. rewrite s5_ch_spine.
destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); [rewrite Hra; exact H2 | exact H1].
Qed.

Section h.
Variable B : asyms.

(* The bytes S5 must give back unchanged at C6, by offset from the cut's sp0 / sp1 / F / shF:
   the six spill words [sp1+24, sp1+96), the 13 saved words [sp0-104, sp0), the frame's flag word
   [F+16376, F+16384), `mac` [F+112, F+118), and the frame shadow outside the `expect` row (shF+[0,28) and
   shF+[1141,1176)).  The `expect` row shF+[28,1141) is the pair set_shadow_00 / set_shadow_f8 works on. *)
Definition s5_prot (sp0 sp1 F sF a : Z) : Prop :=
(sp1 + 24 <= a < sp1 + 96) \/ (sp0 - 104 <= a < sp0) \/ (F + 16376 <= a < F + 16384) \/ (F + 112 <= a < F + 118) \/
(sF <= a < sF + 28) \/ (sF + 1141 <= a < sF + 1176).
Definition s5_row (sF a : Z) : Prop := sF + 28 <= a < sF + 1141.


(* ---- the symbolic state at C5.  Atoms: the registers are their own atoms (`sr_atoms`), 32 is `body` and 33 is
   `n''`; every other value the block needs is an offset of a register atom -- `expect` = s7 + 224,
   `mac` = s7 + 112, `F` = s7, `shF + 0x1c` = s3 + 28.
     region 0: the function's own spill slots [sp + 0x18, sp + 0x60), READ-ONLY (S5 writes none of them), with the
               six words the cut names: [s1+0x18] expect, [s1+0x20] shF+0x1c, [s1+0x28] F, [s1+0x30] mac,
               [s1+0x38] n'', [s1+0x58] body. ---- *)
Definition s5_spills : list YP09.chunk :=
[ YP09.mkChunk 0x18 (CVal 8 (SOff 23 224));
  YP09.mkChunk 0x20 (CVal 8 (SOff 19 28));
  YP09.mkChunk 0x28 (CVal 8 (SOff 23 0));
  YP09.mkChunk 0x30 (CVal 8 (SOff 23 112));
  YP09.mkChunk 0x38 (CVal 8 (SOff 33 0));
  YP09.mkChunk 0x58 (CVal 8 (SOff 32 0)) ].
Definition s5_spill_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x18 0x60 0 0 s5_spills.
Definition s5_extra (body nn : Z) : list word := [Z_to_bv 64 body; Z_to_bv 64 nn].

(* The caller chain at a call of the walk: cgif_file_fuzzer A/ACf5.v:172-186 `rt_chain`, image-free, copied. *)
Lemma s5_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- replace (spZ regs - 8) with (spZ regs + -8) in H8 by lia. replace (spZ regs - 16) with (spZ regs + -16) in H16 by lia.
apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
[replace (spZ regs - 8) with (spZ regs + -8) by lia; exact H8 | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact H16
| exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.

(* The six spill words the walk reloads, at a state (W, mem). *)
Definition s5_spills_at (W : world SEGS) (mem : word -> option byte) (sp1 F sF body nn : Z) : Prop :=
rdword (aview SEGS (w_H W) mem) (sp1 + 24) = Some (F + 224) /\
rdword (aview SEGS (w_H W) mem) (sp1 + 32) = Some (sF + 28) /\
rdword (aview SEGS (w_H W) mem) (sp1 + 40) = Some F /\
rdword (aview SEGS (w_H W) mem) (sp1 + 48) = Some (F + 112) /\
rdword (aview SEGS (w_H W) mem) (sp1 + 56) = Some nn /\
rdword (aview SEGS (w_H W) mem) (sp1 + 88) = Some body.
Lemma s5_spills_kept : forall W W' mem mem' sp1 F sF body nn,
(forall a, sp1 + 24 <= a < sp1 + 96 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
s5_spills_at W mem sp1 F sF body nn -> s5_spills_at W' mem' sp1 F sF body nn.
Proof.
intros W W' mem mem' sp1 F sF body nn Hk (H1 & H2 & H3 & H4 & H5 & H6).
repeat split; [rewrite <- H1 | rewrite <- H2 | rewrite <- H3 | rewrite <- H4 | rewrite <- H5 | rewrite <- H6];
apply rdword_ext; intros k Hk'; apply Hk; lia.
Qed.
(* The block entry: a symbolic state with the spill region, rebuilt from the registers and the spill words. *)
Lemma s5_entry : forall (W : world SEGS) regs mem pc sp1 F sF body nn,
getr regs 9 = Z_to_bv 64 sp1 -> getr regs 23 = Z_to_bv 64 F -> getr regs 19 = Z_to_bv 64 sF ->
0 <= sp1 -> sp1 + 96 <= 2 ^ 64 -> 0 <= F -> F + 224 < 2 ^ 64 -> 0 <= sF -> sF + 28 < 2 ^ 64 ->
0 <= body < 2 ^ 64 -> 0 <= nn < 2 ^ 64 ->
s5_spills_at W mem sp1 F sF body nn ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s5_extra body nn)))
(mkSS pc sr_atoms [s5_spill_region] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc sp1 F sF body nn R9 R23 R19 H1 H2 H3 H4 H5 H6 Hb Hn (V1 & V2 & V3 & V4 & V5 & V6).
set (E := Eimg (Ereg regs (s5_extra body nn))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = body)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nn)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1); apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, s5_spill_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold s5_spills. repeat apply Forall_cons; try apply Forall_nil.
+ apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 23 224) (F + 224));
[cbn [sv_denot]; rewrite U23; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V1).
+ apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 19 28) (sF + 28));
[cbn [sv_denot]; rewrite U19; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V2).
+ apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 23 0) F);
[cbn [sv_denot]; rewrite U23, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V3).
+ apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 23 112) (F + 112));
[cbn [sv_denot]; rewrite U23; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V4).
+ apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 33 0) nn);
[cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V5).
+ apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 32 0) body);
[cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V6).
- cbn. tauto.
- unfold facts_ok; cbn; tauto.
Qed.

(* The callee-saved registers the block relies on: sp = s1 = sp1, s0 = sp0, gp, tp, s3 = shF, s7 = F, s8 = n'. *)
Definition s5_rk (sp0 sp1 F sF np : Z) (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 sp1 /\ getr regs 3 = YG0d.w64 (as_gp B) /\ getr regs 4 = YG0d.w64 (as_tp B) /\
getr regs 8 = Z_to_bv 64 sp0 /\ getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 19 = Z_to_bv 64 sF /\
getr regs 23 = Z_to_bv 64 F /\ getr regs 24 = Z_to_bv 64 np.
Lemma s5_rk_pres : forall sp0 sp1 F sF np regs regs',
aregs_preserved regs regs' -> s5_rk sp0 sp1 F sF np regs -> s5_rk sp0 sp1 F sF np regs'.
Proof.
intros sp0 sp1 F sF np regs regs' HP (R2 & R3 & R4 & R8 & R9 & R19 & R23 & R24).
repeat split;
[ rewrite <- R2 | rewrite <- R3 | rewrite <- R4 | rewrite <- R8 | rewrite <- R9 | rewrite <- R19 | rewrite <- R23 | rewrite <- R24 ];
first [ exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
| exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact (HP 8 ltac:(unfold acallee_saved; lia))
| exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact (HP 19 ltac:(unfold acallee_saved; lia))
| exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact (HP 24 ltac:(unfold acallee_saved; lia)) ].
Qed.
Lemma s5_rk_kept : forall sp0 sp1 F sF np regs regs',
(forall r, In r [2; 3; 4; 8; 9; 19; 23; 24]%bv -> getr regs' r = getr regs r) ->
s5_rk sp0 sp1 F sF np regs -> s5_rk sp0 sp1 F sF np regs'.
Proof.
intros sp0 sp1 F sF np regs regs' HK (R2 & R3 & R4 & R8 & R9 & R19 & R23 & R24).
repeat split; rewrite HK by (cbn; tauto); assumption.
Qed.

(* `seqz s2, (s8 xor 8904)` (0x82ec0-0x82ecc). *)
Lemma s5_seqz_xor : forall x : word,
bv_unsigned (alu64 ALU_SLTU (alu64 ALU_XOR x (Z_to_bv 64 8904)) (Z_to_bv 64 1)) = (if bv_unsigned x =? 8904 then 1 else 0).
Proof.
intros x. rewrite YO0c.seqz_unsigned, YO0c.alu64_xor. change (bv_unsigned (Z_to_bv 64 8904)) with 8904.
destruct (Z.eqb_spec (Z.lxor (bv_unsigned x) 8904) 0) as [H|H]; destruct (Z.eqb_spec (bv_unsigned x) 8904) as [H'|H']; try reflexivity.
- exfalso. apply H'. apply Z.lxor_eq_0_iff. exact H.
- exfalso. apply H. rewrite H'. reflexivity.
Qed.

End h.
End f.
End d.
Print Assumptions s5_ch_spine.
Print Assumptions s5_ctx_in.
Print Assumptions s5_chain.
Print Assumptions s5_spills_kept.
Print Assumptions s5_entry.
Print Assumptions s5_rk_pres.
Print Assumptions s5_rk_kept.
Print Assumptions s5_seqz_xor.
