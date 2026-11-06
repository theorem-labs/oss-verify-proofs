(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan harness walk (LLVMFuzzerTestOneInput 0x7e68c,
   fuzz_qdisc.asan sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain3.v at origin/ossv/recipes 6ebe35ba632 (its segment skeleton: rt_prelude, a
   read-only region added with ast_ok_add_region, the shadow-checked load, pin_by, ra_join_win, rt_hand), with its module
   paths changed; knock's input-byte read is replaced by a read of the frame-rate table in .rodata, and the image-word and
   zero-shadow lemmas are restated from this image's lib/A/AD1k.v (val_mem_img :24-35, img_rd_of_aview :58-65,
   rodata_zero_shadow :208-214) so that this file does not depend on AD1k's uncompiled chain (h-small-a3).
   rule 24 (reuse): no function is proved here; this is SEGMENT S2, the frame-rate read of LLVMFuzzerTestOneInput's walk,
   from ss_J (pc 0x7e7a8) to ss_C (pc 0x7e7c4), both lib/A/QPgLoop0.v.

   THE CODE (capstone 5.0.7 over the pinned image)
     0x7e7a8  slli a0,a1,2 / add a0,s7,a0      a0 = 0x20c80 + 4 * sel   (s7 = 0x20c80, a1 = sel = SOff N_sel 0)
     0x7e7b0  srli a1,a0,3 / add a1,a1,s3 / lb a1,0(a1) / bnez a1 -> 0x7e810    shadow check of &fps[sel]
     0x7e7c0  lw   s2,0(a0)                    s2 = fps[sel]
   The engine's shadow-check token (lib/Reusable/YCbn.v tok_load / tok_branch) turns the four-instruction check into ONE
   range_addressable obligation over [0x20c80 + 4 * sel, +4); the report block at 0x7e810 is never stepped.

   THE PATHS, and the fact that decides each:
   - the shadow obligation (one goal, sel symbolic): paid from the image's zero shadow over .rodata
     (qd_rodata_addressable: AR_laws' al_zshadow at TfibSyms' zero-shadow range (0x10000, 0x20c98 - 0x10000),
     zero_shadow_range, then range_addressable_sub with 0x20c80 <= 0x20c80 + 4 * sel and 0x20c80 + 4 * sel + 4 <= 0x20c98
     from INV_J's 0 <= sel <= 5 through qd_U_fps_addr).
   - `lw s2,0(a0)` needs a concrete offset, so the walk splits on sel: INV_J's 0 <= sel <= 5 gives the six paths
     sel = 0, 1, 2, 3, 4, 5. On path k, a0 is pinned to the literal 0x20c80 + 4 * k (pin_by over INV_J's
     ew E N_sel = Z_to_bv 64 k) and the load reads the base-None region qd_fps_region, whose six 4-byte chunks are the
     table's words 8000, 4000, 0, -1 (0xffffffff), 96000, 2147483647, each paid by qd_val_rom from rt_base's
     arodata_ok (carried to the current memory by arodata_ok_journal), TfibLib's tl_lib_consts at lib_const_addr's
     second range [0x20c80, 0x20c98), and the bytes of the pinned image (qd_rom_chk, vm_compute).
   - all six paths join ss_C the same way: s2 (x18) is pointed at the fresh atom N_fps = 307 holding qd_fps k
     (add_atom_win + pin_by), ra_join_win drops the table region and the dead registers, and INV_C takes sel := k.

   Section hypotheses: TL : TfibLib B, LAWS : AR_laws tfibsegs B (as every segment) and HB : AF0m.TfibSyms B (for the
   .rodata zero shadow: the caller supplies AD2l.TfibB_syms). *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw1 AWalkFw2 ACfm QPgRt QPgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the 24 bytes of LLVMFuzzerTestOneInput.fps at 0x20c80 (.rodata), as six 4-byte literal chunks: 8000, 4000, 0, -1,
   96000, 2147483647 (read from the pinned file; -1 is its low 32 bits 0xffffffff, which `lw` sign-extends) *)
Definition qd_fps_region : YP09.region :=
YP09.mkRegion None 0x20c80 0x20c98 0 0
[ YP09.mkChunk 0x20c80 (CVal 4 (SLit 8000)); YP09.mkChunk 0x20c84 (CVal 4 (SLit 4000));
  YP09.mkChunk 0x20c88 (CVal 4 (SLit 0)); YP09.mkChunk 0x20c8c (CVal 4 (SLit 4294967295));
  YP09.mkChunk 0x20c90 (CVal 4 (SLit 96000)); YP09.mkChunk 0x20c94 (CVal 4 (SLit 2147483647)) ].
(* [lib/A/AD1k.v:24-27 img_cell_chk]: the n bytes of the pinned image at a are the little-endian bytes of v *)
Definition qd_rom_chk (a : Z) (n : nat) (v : Z) : bool :=
forallb (fun k => match img_byte tfibsegs (a + Z.of_nat k) with
| Some b => Z.eqb (bv_unsigned b) (bv_unsigned (Z_to_bv 8 (le_byte v n k)))
| None => false end) (seq 0 n).
(* the image's first segment [0x10000, 0x2f000) is read-only *)
Lemma qd_in_ro_low : forall a, 0x10000 <= a < 0x2f000 -> in_ro_tfa a.
Proof.
intros a Ha. left. eexists. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
lazymatch goal with |- ?lo <= _ < _ + ?sz =>
let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end. lia.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* [lib/A/AD1k.v:28-35 val_mem_img with :58-65 img_rd_of_aview]: an image word under lib_const_addr, from arodata_ok *)
Lemma qd_val_rom : forall B H m a n v, TfibLib B -> arodata_ok B (aview tfibsegs H m) ->
(forall k, (k < n)%nat -> lib_const_addr (a + Z.of_nat k) /\ 0x10000 <= a + Z.of_nat k < 0x2f000) ->
qd_rom_chk a n v = true -> val_mem tfibsegs (mrestrict H m) a n v.
Proof.
intros B H m a n v TL HR Hin Hc k Hk.
pose proof (proj1 (forallb_forall _ _) Hc k ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
destruct (Hin k Hk) as [Hl Hr]. destruct (tl_lib_consts B TL _ Hl) as [Ho He].
pose proof (HR _ (qd_in_ro_low _ Hr) Ho He) as Hv. unfold aview in Hv. unfold img_byte in Hb.
destruct (mbyte tfibsegs (mrestrict H m) (a + Z.of_nat k)) as [b|]; destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b'|];
cbn in Hv; try discriminate.
injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv. apply Z.eqb_eq. exact Hb.
Qed.
(* [lib/A/AD1k.v:208-214 rodata_zero_shadow, with YG0v.zero_shadow_range]: .rodata up to the table's end is addressable *)
Lemma qd_rodata_addressable : forall B ly S W mem md, AF0m.TfibSyms B -> AR_laws tfibsegs B -> AR tfibsegs B ly S W mem md ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10000 (0x20c98 - 0x10000).
Proof.
intros B ly S W mem md HB LAWS HAR. apply zero_shadow_range; [reflexivity | reflexivity |].
exact (al_zshadow _ _ LAWS ly S W mem md (0x10000, 0x20c98 - 0x10000) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (AF0m.ts_zsh B HB); cbn; tauto)).
Qed.
(* the engine's address of fps[sel]: (sel << 2) + 0x20c80 *)
Lemma qd_U_fps_addr : forall E n s, ew E n = Z_to_bv 64 s -> 0 <= s <= 5 ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SLit 134272)) = 134272 + 4 * s.
Proof.
intros E n s Hn Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SLit, (U_atom E n s Hn) by lia. change (Z.land (zcanon 2) 63) with 2. change (zcanon 134272) with 134272.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (s * 4)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End r.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HB : AF0m.TfibSyms B.
Lemma rt_S2 : forall fuel : nat,
  rt_from B MT FP POST ss_C (INV_C B MT fuel) -> rt_from B MT FP POST ss_J (INV_J B MT fuel).
Proof.
intros fuel RC. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & Hin0 & Hrq & cur & rem & bud & c & lead & sel & Ecur & Erem & Ebud & Elead & Esel &
HCUR & Hbud & Hfuel & Hlead & Hsel).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pose proof (arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD) as HROD3.
(* the table region, read-only, its six words from the image *)
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv qd_fps_region HS eq_refl) as HS3;
specialize (HS3 ltac:(
  unfold region_ok, qd_fps_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
  split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
  repeat (apply Forall_cons; [ eapply (chunk_ok_val tfibsegs _ _ 0 _ 4 (SLit _)); [reflexivity | cbn; lia | cbn; lia |
    rewrite Z.add_0_l; apply (qd_val_rom B _ _ _ _ _ TL HROD3);
    [intros kk Hkk; unfold lib_const_addr; cbn in Hkk; lia | vm_compute; reflexivity] ] | ]);
  apply Forall_nil));
specialize (HS3 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
  let ry2 := eval vm_compute in ry in let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; unfold A_GOT_shadow, A_shadow_glob;
  repeat split; zone_lia));
clear HS; rename HS3 into HS; norm_ss HS end.
(* 0x7e7a8 .. 0x7e7c0: the run stops at `lw` (symbolic address), after the one shadow obligation *)
pl_run_to HS HJ3 AG 0x7e7c4.
1: { rewrite (U_atom E 32 SB E32n) by (unfold SB; lia). rewrite (qd_U_fps_addr E 306 sel Esel Hsel).
rewrite SB_SHADOW_OFF.
eapply range_addressable_sub; [exact (qd_rodata_addressable B ly3 S3 W3 (ms_mem ms3) md3 HB LAWS (proj1 HJ3)) | lia | lia]. }
(* the six selector paths *)
assert (Hs6 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5) by lia.
destruct Hs6 as [-> | [-> | [-> | [-> | [-> | ->]]]]].
all: lazymatch type of Esel with _ = Z_to_bv 64 ?kk =>
let ad := eval vm_compute in (134272 + 4 * kk) in
pin_by HS (10%bv : bv 5) (SLit ad) ltac:(cbn [sv_denot]; ewpeel; rewrite Esel; vm_compute; reflexivity);
pl_run_to HS HJ3 AG 0x7e7c4;
add_atom_win HS 307%nat (Z_to_bv 64 (qd_fps kk)) Efps;
pin_by HS (18%bv : bv 5) (SOff 307 0) ltac:(rewrite sv_denot_SOff0, Efps; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity) end.
all: ra_join_win HS ss_C 720%nat ql_deadsC_bv ltac:(idtac).
all: rebaseE HS AG HEv.
all: clear HEv.
all: relowRT HS AG E10 E11 E32 E10n E11n E32n.
all: rt_hand RC HS.
all: split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm3|]; split; [exact Hin0|]; split; [exact Hrq|].
all: lazymatch type of Esel with _ = Z_to_bv 64 ?kk => exists cur, rem, bud, c, lead, kk end.
all: split; [exact Ecur|]; split; [exact Erem|]; split; [exact Ebud|]; split; [exact Elead|]; split; [exact Efps|].
all: split; [exact HCUR|]; split; [exact Hbud|]; split; [exact Hfuel|]; split; [exact Hlead|]; lia.
Qed.
End c.
End b.
