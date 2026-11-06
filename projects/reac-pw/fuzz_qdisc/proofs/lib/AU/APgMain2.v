(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan harness walk (LLVMFuzzerTestOneInput 0x7e68c,
   fuzz_qdisc.asan sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain3.v at origin/ossv/recipes 6ebe35ba632 (its segment skeleton: rt_prelude, a
   read-only region added with ast_ok_add_region, the shadow-checked load, pin_by, ra_join_win, rt_hand), with its module
   paths changed; knock's input-byte read is replaced by a read of the frame-rate table in .rodata, and the zero-shadow
   lemma is restated from that image's lib/A/AD1k.v (rodata_zero_shadow :208-214).
   rule 24 (reuse): no function is proved here; this is SEGMENT S2, the frame-rate read of LLVMFuzzerTestOneInput's walk. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgMain2.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062):
   SEGMENT S2 from ss_J (pc 0x7e78c, INV_J fuel) to ss_C (pc 0x7e7a0, INV_C fuel), both lib/AU/APgLoop0.v. Written by
   hand from the A file, with the lib/AU imports and the asan-ubsan pcs. What differs:
   - the asan-ubsan code forms the table address before ss_J (lib/AU/APgMain1.v), so a0 (x10) is already the atom
     N_fpa = 309 with INV_J's ew E N_fpa = Z_to_bv 64 (0x20c80 + 4 * sel); the A file's `slli a0,a1,2 / add a0,s7,a0`
     (A 0x7e7a8-0x7e7ac) and its lemma qd_U_fps_addr are gone, and the obligation reads U (SOff N_fpa 0) by U_atom;
   - qd_rom_chk, qd_in_ro_low and qd_val_rom are lib/AU/APgLoop0.v's (that file carries them for this walk and the
     calls), so this file restates only the table region and qd_rodata_addressable;
   - the zero-shadow row (0x10000, 0x20c98 - 0x10000) is the first row of lib/AU/YF0m.v's Tfib_zero_shadow, and the
     table's 24 bytes at 0x20c80 (lib_const_addr's second range [0x20c80, 0x20c98), lib/AU/YCeh.v) are the same six
     words as in the asan image; qd_rom_chk checks them against the pinned asan-ubsan image (vm_compute).

   THE CODE (capstone 5.0.7 over the pinned image)
     0x7e78c  srli a1,a0,3 / add a1,a1,s3 / lb a1,0(a1) / bnez a1 -> 0x7e814    shadow check of &fps[sel], a0 = N_fpa
              (slow block 0x7e814 `andi a2,a0,7 / addi a2,a2,3 / blt a2,a1 -> 0x7e79c`, then `j` to the report
              call 0x7e894)
     0x7e79c  lw   s2,0(a0)                    s2 = fps[sel]
   The engine's shadow-check token (lib/Reusable/YCbn.v tok_load / tok_branch) turns the check into ONE
   range_addressable obligation over [0x20c80 + 4 * sel, +4); the slow block and the report are never stepped.

   THE PATHS, and the fact that decides each:
   - the shadow obligation (one goal, sel symbolic): paid from the image's zero shadow over .rodata
     (qd_rodata_addressable: AR_laws' al_zshadow at TfibSyms' zero-shadow range (0x10000, 0x20c98 - 0x10000),
     zero_shadow_range, then range_addressable_sub with 0x20c80 <= 0x20c80 + 4 * sel and 0x20c80 + 4 * sel + 4 <= 0x20c98
     from INV_J's N_fpa equation and 0 <= sel <= 5).
   - `lw s2,0(a0)` needs a concrete offset, so the walk splits on sel: INV_J's 0 <= sel <= 5 gives the six paths
     sel = 0, 1, 2, 3, 4, 5. On path k, a0 is pinned to the literal 0x20c80 + 4 * k (pin_by over INV_J's
     ew E N_fpa = Z_to_bv 64 (0x20c80 + 4 * k)) and the load reads the base-None region qd_fps_region, whose six 4-byte
     chunks are the table's words 8000, 4000, 0, -1 (0xffffffff), 96000, 2147483647, each paid by qd_val_rom from
     rt_base's arodata_ok (carried to the current memory by arodata_ok_journal), TfibLib's tl_lib_consts at
     lib_const_addr's second range, and the bytes of the pinned image (qd_rom_chk, vm_compute).
   - all six paths join ss_C the same way: s2 (x18) is pointed at the fresh atom N_fps = 307 holding qd_fps k
     (add_atom_win + pin_by), ra_join_win drops the table region and the dead registers (a0 among them), and INV_C
     takes sel := k.

   Section hypotheses: TL : TfibLib B, LAWS : AR_laws tfibsegs B (as every segment) and HB : YF0m.TfibSyms B (for the
   .rodata zero shadow). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the 24 bytes of LLVMFuzzerTestOneInput.fps at 0x20c80 (.rodata), as six 4-byte literal chunks: 8000, 4000, 0, -1,
   96000, 2147483647 (-1 is its low 32 bits 0xffffffff, which `lw` sign-extends); each chunk is checked against the
   pinned asan-ubsan image by qd_rom_chk in rt_S2 *)
Definition qd_fps_region : YP09.region :=
YP09.mkRegion None 0x20c80 0x20c98 0 0
[ YP09.mkChunk 0x20c80 (CVal 4 (SLit 8000)); YP09.mkChunk 0x20c84 (CVal 4 (SLit 4000));
  YP09.mkChunk 0x20c88 (CVal 4 (SLit 0)); YP09.mkChunk 0x20c8c (CVal 4 (SLit 4294967295));
  YP09.mkChunk 0x20c90 (CVal 4 (SLit 96000)); YP09.mkChunk 0x20c94 (CVal 4 (SLit 2147483647)) ].
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* [lib/A/QPgMain2.v qd_rodata_addressable, with YG0v.zero_shadow_range]: .rodata up to the table's end is addressable *)
Lemma qd_rodata_addressable : forall B ly S W mem md, YF0m.TfibSyms B -> AR_laws tfibsegs B -> AR tfibsegs B ly S W mem md ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10000 (0x20c98 - 0x10000).
Proof.
intros B ly S W mem md HB LAWS HAR. apply zero_shadow_range; [reflexivity | reflexivity |].
exact (al_zshadow _ _ LAWS ly S W mem md (0x10000, 0x20c98 - 0x10000) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (YF0m.ts_zsh B HB); cbn; tauto)).
Qed.
End r.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HB : YF0m.TfibSyms B.
Lemma rt_S2 : forall fuel : nat,
  rt_from B MT FP POST ss_C (INV_C B MT fuel) -> rt_from B MT FP POST ss_J (INV_J B MT fuel).
Proof.
intros fuel RC. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & Hin0 & Hrq & cur & rem & bud & c & lead & sel & Ecur & Erem & Ebud & Elead & Efpa &
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
(* 0x7e78c .. 0x7e79c: the run stops at `lw` (symbolic address), after the one shadow obligation *)
pl_run_to HS HJ3 AG 0x7e7a0.
1: { rewrite (U_atom E 32 SB E32n) by (unfold SB; lia). rewrite (U_atom E 309 (134272 + 4 * sel) Efpa) by lia.
rewrite SB_SHADOW_OFF.
eapply range_addressable_sub; [exact (qd_rodata_addressable B ly3 S3 W3 (ms_mem ms3) md3 HB LAWS (proj1 HJ3)) | lia | lia]. }
(* the six selector paths *)
assert (Hs6 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5) by lia.
destruct Hs6 as [-> | [-> | [-> | [-> | [-> | ->]]]]].
all: lazymatch type of Efpa with _ = Z_to_bv 64 (134272 + 4 * ?kk) =>
let ad := eval vm_compute in (134272 + 4 * kk) in
pin_by HS (10%bv : bv 5) (SLit ad) ltac:(cbn [sv_denot]; ewpeel; rewrite Efpa; vm_compute; reflexivity);
pl_run_to HS HJ3 AG 0x7e7a0;
add_atom_win HS 307%nat (Z_to_bv 64 (qd_fps kk)) Efps;
pin_by HS (18%bv : bv 5) (SOff 307 0) ltac:(rewrite sv_denot_SOff0, Efps; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity) end.
all: ra_join_win HS ss_C 720%nat ql_deadsC_bv ltac:(idtac).
all: rebaseE HS AG HEv.
all: clear HEv.
all: relowRT HS AG E10 E11 E32 E10n E11n E32n.
all: rt_hand RC HS.
all: split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm3|]; split; [exact Hin0|]; split; [exact Hrq|].
all: lazymatch type of Efps with _ = Z_to_bv 64 (qd_fps ?kk) => exists cur, rem, bud, c, lead, kk end.
all: split; [exact Ecur|]; split; [exact Erem|]; split; [exact Ebud|]; split; [exact Elead|]; split; [exact Efps|].
all: split; [exact HCUR|]; split; [exact Hbud|]; split; [exact Hfuel|]; split; [exact Hlead|]; lia.
Qed.
End c.
End b.
