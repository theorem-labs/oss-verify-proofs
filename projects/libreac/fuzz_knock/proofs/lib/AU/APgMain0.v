(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMain0.v of this library (segment S0 ENTRY,
   knock_lib_A_seg), for fuzz_knock's ASan-UBSan image (fuzz_knock.asan-ubsan, sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), made the way
   proofs/cgif/cgif_file_fuzzer/lib/YCez.v is made from lib/A/ACez.v at c8557374ad2e: the walk framework imports move
   to the asan-ubsan twins (lib/AU) and every address is re-derived on the asan-ubsan bytes. rule 24: no function
   proved (a twin of a port of the released cgif_file_fuzzer harness walk). *)

(* SEGMENT S0 ENTRY of LLVMFuzzerTestOneInput (0x7eed0, 0x578 bytes in this image): pc 0x7eed0-0x7f000 (77
   instructions), ends at ss_H, pc 0x7f004. Every address below was read from the pinned asan-ubsan bytes (capstone
   5.0.7 over the file, sha256 checked; symbols from the debug twin, whose loaded bytes differ from the pin only in the
   25 build-id bytes) and compared instruction by instruction with the asan image's S0. The 77 instructions keep their
   pcs and operations; three things differ, each re-derived by its meaning:
   - the GOT slots: auipc 0x7ef1c / 0x7ef20 with ld 0x6fc / 0x750 read 0x96618 (it holds 0x9e578,
     __asan_shadow_memory_dynamic_address) and 0x96670 (it holds 0x9e580, __asan_option_detect_stack_use_after_return):
     YCeh's A_GOT_shadow / A_shadow_glob / A_GOT_uar / A_uar_glob, and the four cell regions of ss_H.
   - the registers after the stack_malloc call: F goes to a6 and a7 (mv a6,a0 at 0x7ef48, mv a7,a6 at 0x7ef54, bnez a6
     at 0x7ef58, the header stores through a7, sd a7,80(s1) at 0x7ef78, sd a6,24(s1) at 0x7f000), one register above
     the asan image's. So a5 keeps the fresh atom 80 that reseat gives it, and a6 = a7 = F (atom 75).
   - the size test 0x7effc bnez a1 targets 0x7f2e4 (the retired-frame epilogue, lui a0,0x45e03, as in the asan image);
     its taken side is refuted the same way.
   No UBSan trap site is in S0: the harness's branches into unimp words are at 0x7f010 and above (auditor list,
   (internal path) section 3), and none of the six branches in
   0x7eed0-0x7f000 (0x7ef3c, 0x7ef44, 0x7ef4c, 0x7ef58, 0x7ef70, 0x7effc) targets an unimp word.
   Re-measured and unchanged: __asan_stack_malloc_1 = 0x3c064 (jal at 0x7ef44, a0 = 0x80 at 0x7ef40: class 1, RA
   0x7ef48); the first stop 0x7ef14; the 192-byte save frame and andi sp,sp,-0x20; the spills 24 / 56 / 80(s1); the
   UAR test at 0x7ef3c and the UAR-off path 0x7ef50; the probe loop 0x7ef5c-0x7ef74; the frame header 0x41b58ab3 /
   0x1e6a5 / 0x7eed0; the 16 poison bytes 0x7efb8-0x7eff8. YCfm's harness constants: A_LLVMF 0x7eed0, RA_LLVMF
   0x7edcc (target_run's jal 0x7edc8), A_EMPTY 0x5d0be0 (target_run.initialized 0x5d0bd0, formed at 0x7ed34 /
   0x7ed38, + 16 at 0x7edac; nm oft_aligned_copy.empty).

   The walk is lib/A/APgMain0.v's, step for step (its comment gives each step and the donor line it follows); the
   only proof changes are the ones the missing APgRt twin forces (below) and ss_H's registers and cells.

   Statement: lib/A/APgMain0.v's, with the premise 0 <= T that trunk's APgRt rt_base conjunct ACC0 <= c_T cx needs
   (lib/A/APgRt.v), in the place the A file's fix puts it.

   Section hypotheses (all named; the file states no axiom of its own):
     MTL : ameter_laws MT;  TL : TfibLib B;  LAWS : AR_laws tfibsegs B;  ML : model_laws (as_universe B);
     ASM1 : astack_malloc_realizes tfibsegs B 1;  SMP : stack_malloc_progressP B;  FFL : frame_flag_lawP tfibsegs B;
     MTF : ameter_fs_laws MT;
     RB : rt_from B MT FP POST ss_H (INV_0 B MT 0).
   The stack_malloc call is the lemma aj_stack_malloc_atS of lib/Reusable/YC85.v, as in lib/A/APgMain0.v.
   lib/AU/APgRt.v (a Theorem Labs lane's asan-ubsan twin of lib/A/APgRt.v) now holds the context record, so the names this
   file takes from it are that file's definitions, imported, not Section Variables with equation hypotheses:
     rtcx, mkRTCX and the projections c_ly .. c_T (the record, APgRt.v:37-40); rt_base (:43-55, whose last conjunct
     is ACC0 <= c_T cx and whose rt_base_eq writes ACC0 as its value 0); rt_F, rt_FL, rt_E (:57-61); rt_from
     (:64-74); INV_0 (:75-76); rt_extra, rt_regions0, rt_atoms0, ss_rt0 (:31-36); and the lemma rt_entry (:158-218).
     RTBx / RTBspan (:29-30) are written as their bodies at their uses, and the Ltac awrRT_rec / awrRT / keptRT
     (:272-331) come from APgRt too.
   Local lemma: denot_and_m32, as in lib/A/APgMain0.v (donor A/ACer.v:156-164; lib/AU/AWalkFw1 leaves it out too).

  Imports: the asan-ubsan twins of the walk framework, lib/AU (derive_y.py over
  lib/A): AWalkFw0 (tfibsegs = AsanUbsan.M.loaded_segments), YCef (tfibtbl_lib over 0x7ea30 / 824), YF0l
  (Tfib_code, pc_stack_malloc 1 = 0x3c064), YCej, YCeh (TfibLib, the GOT cells above, SB, frm_off_img, shok_auto,
  zone_lia), YCem, YCep, AWalkFw1, AWalkFw2, YCfm (the harness constants above, EV_LIB = 0). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI16 YM05 YC85.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm APgRt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ss_H: the state at 0x7f004, the S0 -> S1 boundary (the form of the donor's ss_A2, A/ACf7.v:27-28; lib/A/APgMain0.v's
   ss_H with this image's registers and cells). Registers: ra / t0-t2 / a5 / t3-t6 are the fresh atoms 71..74, 80,
   83..86 that reseat gives after the stack_malloc call (a0 got 75 = F, the donor's numbering); s0 = sp0, sp = s1 =
   sp1 (atom 70); a0 = -13 (0x7efac), a1 = n >> 26 (0x7efc8), a2 = 0x7eed0 (0x7ef84/0x7ef9c), a3 = -8, a4 = -15,
   a6 = a7 = F, s3 = p, s4 = n, s6 = SB + F/8 (atom 88, through the alias). Memory: the 16 frame shadow bytes (region
   88), the frame header and the flag pointer (region 75), the spills 24 / 56 / 80(s1) (region 70), the twelve saves
   (region 2), the GOT slots 0x96618 / 0x96670 and the shadow / uar cells 0x9e578 / 0x9e580. Facts: the donor's seven
   atoms (88, 87, 75, 70, 2, 11, 32), the condition (n >> 26) = 0 from the 0x7effc split, the shadow alias. *)
Definition ss_H : sstate :=
mkSS 520196
[SLit 0; SOff 71 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 2 0; SOff 70 0;
 SLit 18446744073709551603; SAlu ALU_SRL (SOff 11 0) (SLit 26); SLit 519888; SLit 18446744073709551608;
 SLit 18446744073709551601; SOff 80 0; SOff 75 0; SOff 75 0; SOff 18 0; SOff 10 0; SOff 11 0; SOff 21 0;
 SOff 88 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 83 0; SOff 84 0; SOff 85 0; SOff 86 0]
[ YP09.mkRegion (Some 88%nat) 0 16 0 16
  [YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603))];
  YP09.mkRegion (Some 75%nat) 0 128 0 128
  [YP09.mkChunk 16 (CVal 8 (SLit 519888)); YP09.mkChunk 8 (CVal 8 (SLit 124581));
   YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 120 (CVal 8 (SOff 87 0))];
  YP09.mkRegion (Some 70%nat) 16 88 16 88
  [YP09.mkChunk 24 (CVal 8 (SOff 75 0)); YP09.mkChunk 80 (CVal 8 (SOff 75 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
  YP09.mkRegion None 615960 615968 0 0 [YP09.mkChunk 615960 (CVal 8 (SLit 648568))];
  YP09.mkRegion None 648568 648576 0 0 [YP09.mkChunk 648568 (CVal 8 (SOff 32 0))];
  YP09.mkRegion None 616048 616056 0 0 [YP09.mkChunk 616048 (CVal 8 (SLit 648576))];
  YP09.mkRegion None 648576 648580 0 0 [YP09.mkChunk 648576 (CVal 4 (SLit 1))] ]
None
(mkFacts
 [(88%nat, mkAF 2147451392 17594333495296 2); (87%nat, mkAF 4096 140737479966720 0);
  (75%nat, mkAF 4096 140737479966720 5); (70%nat, mkAF 70368744177152 140737488355328 5);
  (2%nat, mkAF 70368744177664 140737488355328 4); (11%nat, mkAF 0 67108863 0);
  (32%nat, mkAF 2147450880 2147450880 0)]
 [mkAC BC_EQ (SAlu ALU_SRL (SOff 11 0) (SLit 26)) (SLit 0)]
 [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)]).


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
(* donor A/ACer.v:156-164, verbatim except M64_val (lib/YI0s.v:17, not in knock's Reusable) unfolded in place *)
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Hypothesis MTF : ameter_fs_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis RB : rt_from B MT FP POST ss_H (INV_0 B MT 0).
Theorem knock_lib_A_seg : forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n T,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
mo_ok MT S T -> 0 <= T ->
SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
(fun W' c' => exists fpos sp1 E0, POST (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) W' c').
Proof.
intros ly S W regs mem md p n T HPRE Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK HT0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (rt_entry B TL LAWS W ly S regs mem md p n HPRE Hp Hn Hpn) as HS.
unfold ss_rt0, rt_regions0, rt_atoms0, rt_extra in HS.
pose proof (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (HEV : EV_LIB = 0) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
remember (Ereg regs [Z_to_bv 64 SB]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Hp).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros nn Hnn; reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; rewrite HE; apply ew_Ereg_nat; exact Hnn).
clear HE.
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 A_LLVMF).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) mem).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
(* 0x7eed0-0x7ef10: the save frame and andi sp,sp,-0x20; stop at 0x7ef14 (donor :83); RTBspan written as its body *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0x7ef14. { awrRT AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames.
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (sp1_facts (spZ regs + -192) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-192) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 70 Ev (havoc Ev 70 [Z_to_bv 64 sp1]) ssv msv HS
(env_agree_havoc_ge 70 70 Ev Ev _ ltac:(lia) (env_agree_refl 70 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil FFS C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* the stack region keeps the saves [sp0-104, sp0) (donor :111-115 keeps [sp0-96, sp0)) *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* region 70 = [s1+16, s1+88): the spills 16..88(s1) (donor :117-126, [s1, s1+32)) *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 16 88 16 88 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
(* 0x7ef14-0x7ef44: GOT loads, sd a1,0x38(s1), the UAR test (decided), a0 = 0x80, jal 0x3c064; stop by SR_fetch *)
aj_run_tok tfibtbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1). { awrRT AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 245860 with (pc_stack_malloc code 1) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS tfibsegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- clear - Hsp1; lia. - rewrite FFS, Hes; clear - Hsp1; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1. - vm_compute. reflexivity.
- rewrite Hfr0. change (fs_frames 1) with 8192. cbn. clear; lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
(* the class-1 fake frame (donor :153-159 at class 2) *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as Hfin2_img.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [keptRT HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) | match goal with |- ?g => idtac "KEPTFAIL" g end]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E87 : ew Ev 87 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E88 : ew Ev 88 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ 75 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 87 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E88, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias tfibsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB RF ltac:(lia) E32' E88)) as HS3;
clear HS; rename HS3 into HS;
(* region 75 = the 128-byte frame, flag pointer at F+120 = F+128-8 (donor :190-200: 256 bytes, chunk 248) *)
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val tfibsegs Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
(* region 88 = the frame's 16 shadow bytes, zero after stack_malloc (donor :201-221: 32 bytes) *)
assert (ZS : forall j, 0 <= j < 2 -> val_mem tfibsegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _
(fshadow_region 88 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E88, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; rewrite E88, RF; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x7ef48-0x7eff8: bnez a6 decided by HPTR 5 (probe loop never reached), sd a7,80(s1), the frame header, SB from
   56(s1), the 16 poison bytes; the run stops undecided at the size test 0x7effc (donor :223) *)
aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x7f004. { awrRT AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E11v : ew Ev 11 = Z_to_bv 64 n) by (rewrite (AG 11%nat) by lia; exact E11) end.
(* 0x7effc bnez a1 with a1 = n >> 26: split (the form of A/ACf1.v:329-351) *)
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
apply (SRr_sym_branch tfibsegs Wg Ev ssv msF mdF _ BC_NE (SAlu ALU_SRL (SOff 11 0) (SLit 26)) (SLit 0) HS) end end;
clear HS; intros Hc HS.
- (* taken, 0x7effc -> 0x7f2e4: impossible, n < 2^26 *)
exfalso.
rewrite branch_ne_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 11 n E11v) in Hc by lia. rewrite !U_SLit in Hc.
change (Z.land (zcanon 26) 63) with 26 in Hc. change (zcanon 0) with 0 in Hc.
rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small n (2 ^ 26)) in Hc by lia.
vm_compute in Hc. discriminate Hc.
- (* fall-through: the condition (n >> 26) = 0 decides 0x7effc; sd a6,24(s1) at 0x7f000; stop at 0x7f004 *)
clear Hc. norm_ss HS.
aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x7f004. { awrRT AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
rebaseE HS AG HEv. clear HEv.
assert (P1 : c_ly (mkRTCX ly S W regs mem md p n fpos sp1 E T) = ly) by reflexivity.
assert (P2 : c_S (mkRTCX ly S W regs mem md p n fpos sp1 E T) = S) by reflexivity.
assert (P3 : c_W (mkRTCX ly S W regs mem md p n fpos sp1 E T) = W) by reflexivity.
assert (P4 : c_regs (mkRTCX ly S W regs mem md p n fpos sp1 E T) = regs) by reflexivity.
assert (P5 : c_mem (mkRTCX ly S W regs mem md p n fpos sp1 E T) = mem) by reflexivity.
assert (P6 : c_md (mkRTCX ly S W regs mem md p n fpos sp1 E T) = md) by reflexivity.
assert (P7 : c_p (mkRTCX ly S W regs mem md p n fpos sp1 E T) = p) by reflexivity.
assert (P8 : c_n (mkRTCX ly S W regs mem md p n fpos sp1 E T) = n) by reflexivity.
assert (P9 : c_fpos (mkRTCX ly S W regs mem md p n fpos sp1 E T) = fpos) by reflexivity.
assert (P10 : c_sp1 (mkRTCX ly S W regs mem md p n fpos sp1 E T) = sp1) by reflexivity.
assert (P11 : c_E0 (mkRTCX ly S W regs mem md p n fpos sp1 E T) = E) by reflexivity.
assert (P12 : c_T (mkRTCX ly S W regs mem md p n fpos sp1 E T) = T) by reflexivity.
pose proof RB as RB'. rewrite rt_from_eq in RB'. cbv beta in RB'.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply SRr_mono; [eapply (RB' (mkRTCX ly S W regs mem md p n fpos sp1 E T) Ev 0 0 _ _ Wg msF mdF) | cbv beta; intros W' c' _ HPOST; exists fpos, sp1, E; exact HPOST] end end.
all: rewrite ?rt_base_eq, ?rt_E_eq, ?rt_F_eq, ?rt_FL_eq; cbv beta delta [INV_0 ACC0];
rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7, ?P8, ?P9, ?P10, ?P11, ?P12.
+ repeat match goal with |- _ /\ _ => split end; try exact HT0; try assumption; try reflexivity.
+ fold F FL.
split; [exact AG|]. split; [exact E70 | split; [exact RF | split; [exact E87 | exact E88]]].
+ exact HJ2.
+ rewrite Hfrs2, Hfr0. reflexivity.
+ rewrite ES2. apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL).
+ split; [clear; lia | split; [clear; lia | exact Eab]].
+ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (ss_mem ss_H) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
exact HS3.
Qed.
End d.
End b.
