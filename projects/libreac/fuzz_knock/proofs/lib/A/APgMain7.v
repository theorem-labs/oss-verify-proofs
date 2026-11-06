(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_knock: segment S7 EXIT of the ASan harness walk of
   LLVMFuzzerTestOneInput in fuzz_knock.asan (sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118).
   Donor: proofs/cgif/cgif_file_fuzzer/lib/A/ACf4.v:26-127 (the exit lemma and its local tactics) and A/ACf7.v:35-56 (the
   exit state and invariant) at c8557374ad2e. Framework: a Theorem Labs lane, knock's lib/A copies
   under the donor names: AWalkFw0 (tfibsegs), ACef (tfibtbl_lib), AF0l, ACej, ACeh (TfibLib, tfib_img_range with
   TFIB_IMG_END = 0x5f3000), ACem (aj_run_flag_sh), ACep, AWalkFw1 (A/ACer.v), AWalkFw2 (A/ACf9.v), ACfm (EV_LIB = 0), and
   APgRt (the class-1 context record, rt_prelude, fs_rwF with the 0 16 window). *)
(* rule 24: no function proved. A port of the released cgif_file_fuzzer harness-walk structure.

   THE LEMMA
     rt_X : forall B MT FP, ameter_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) ->
            astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B -> ameter_fs_laws MT ->
            rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT)
   and its general form rt_XP (any PX with PXK), as the donor's rt_XP / rt_X.
   Section hypotheses of rt_XP (Section c): B, MT, MTL : ameter_laws MT, FP, TL : TfibLib B, LAWS : AR_laws tfibsegs B,
   ML : model_laws (as_universe B), ASF : astack_free_law tfibsegs B, FFL : frame_flag_lawP tfibsegs B,
   MTF : ameter_fs_laws MT, PX, PXK (PX survives a memory change that keeps the image); Context ROB : ro_tfa_below_ofl.
   These are the donor's hypotheses, unchanged.

   THE CODE (capstone 5.0.7 over the pinned image bytes; the 65 words agree with fuzz_knock.objdump.txt)
     0x7f274-0x7f288  li a0,-8; sb a0,4..8(s6)              repoison the 5 shadow bytes of k (F+32..F+72) to 0xf8
     0x7f28c          ld a5,24(s1)                            a5 = F (stored at 0x7f000 in S0)
     0x7f290          ld a6,16(s1)                            a6 = F (stored at 0x7f088 in S2)
     0x7f294-0x7f29c  lui a0,0x45e03; addiw a0,a0,0x60e; sd a0,0(a6)   retire the frame: F[0] := 0x45E0360E
     0x7f2a0          beqz a5,0x7f2f4                         the real-stack test; NOT taken (see below)
     0x7f2a4-0x7f2e4  li a0,-11; 16 x sb a0,k(s6)             the 16 shadow bytes of the frame := 0xf5
     0x7f2e8-0x7f2ec  ld a0,120(a5); sb zero,0(a0)            *(flag address at F+120) := 0, frees the fake frame
     0x7f2f0          j 0x7f334
     0x7f2f4-0x7f330  16 x sb zero,k(s6)                      the real-stack path: DEAD, never walked
     0x7f334-0x7f374  li a0,0; addi sp,s0,-192; 13 restores (ra, s0-s11 from sp0-8 .. sp0-104); addi sp,sp,192; ret
   Entries into 0x7f274: 0x7f0dc beqz s9 (S2), 0x7f240 bltu s8,s10 and 0x7f24c j (S6). The jal at 0x7f270
   (__asan_report_load1, noreturn) falls through to 0x7f274 in the CFG only; S3's walk discharges its guard (plan risk 7).
   No call and no cut site in 0x7f274-0x7f374.

   THE DEAD REAL-STACK PATH. a5 is the chunk at 24(s1), whose value is SOff 75 0 = F. ss_X carries the atom
   (75, [4096, 2^47 - 2^23], 32-aligned), so the symbolic executor decides beqz a5 as not taken and never enters
   0x7f2f4-0x7f330. The atom is the one S0 sets up after __asan_stack_malloc_1 returns the fake frame (SMP and
   count_cid 1 [] < fs_frames 1; frames_bounds gives 4096 <= F). rt_from keeps frames S3 = [(1, fpos)], so it holds here.

   WHERE KNOCK DIFFERS FROM THE DONOR, AND WHY
   - Frame class 1 (128 B, 16 shadow bytes) for the donor's class 2 (256 B, 32): knock calls __asan_stack_malloc_1
     (a0 = 0x80 at 0x7ef40). So: FFL / HnoF at class 1 and 128 B; fs_rwF's window 0 16; the flag-slot region is
     75 [112,128) with its chunk at 120 (donor [240,256), 248); wrangeRT uses exists 1 / 128 / 16.
   - The fake-frame pointer and the frame are reloaded from the spills 24(s1) / 16(s1). The donor keeps them in s2 / s7.
     So ss_X has region 70 [16,32) (read-only) with chunks 16 and 24 = SOff 75 0, and s2 / s7 are dead in ss_X.
   - 13 saved registers (ra, s0-s11) at sp0-104..sp0-8 (donor: 12, s0-s10, [-96,0)): region 2 [-104,0).
   - ss_X is written out, not taken from a donor-style ss_B (a Theorem Labs lane has no ss_B). Its shadow region 88 [0,16) has no chunks.
     The exit overwrites all 16 bytes, so S2 / S6 only need to give a weaker state (submem / subregion).
   - The PXK step unfolds the image-bound names, so that lia sees knock's 0x10000 / 0x5f3000. Those names are ACeh's
     TFIB_IMG_LO / TFIB_IMG_END and YImgTop.IMG_LO / IMG_TOP, which off_img (Reusable/YCbq.v) also cites. The donor writes
     the literals.
   - add_flag_regionRT drops the donor's `unfold A_GOT_shadow, ...`: ss_X has no constant-address region.
   - rt_post's PX is True (APgRt, signature D5): knock's only return path.

   ADDRESS AND NUMERAL RENAMES (donor -> knock)
     exit pc 0x80878 -> 0x7f274; ret 0x809e0 -> 0x7f374; repoison 0x80878-0x808a0 -> 0x7f274-0x7f288;
     retire 0x808a4-0x808ac -> 0x7f294-0x7f29c; real-stack test 0x808b0 beqz s2 -> 0x7f2a0 beqz a5;
     f5 stores 0x808b4-0x80934 (32) -> 0x7f2a4-0x7f2e4 (16); flag store 0x80938-0x8093c ld 0xf8(s2) -> 0x7f2e8-0x7f2ec
     ld 0x78(a5); j 0x80940 -> 0x7f2f0; dead real-stack path 0x80944-0x809a0 -> 0x7f2f4-0x7f330;
     restore 0x809a8-0x809dc -> 0x7f338-0x7f370; frame 256 -> 128; shadow 32 -> 16; flag slot F+248 -> F+120;
     save area [-96,0) -> [-104,0); rt_X_deads / rt_X_regs per knock's live registers (s0 = SOff 2 0, s1 = sp = SOff 70 0,
     s6 = SOff 88 0, gp / tp kept, the rest dead from slot 600). *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw1 AWalkFw2 ACfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

(* The exit state at 0x7f274 [A/ACf7.v:35-50]. *)
(* Registers: x0; x2 = sp = sp1 (slot 70); gp, tp (x3, x4) as at entry; x8 = s0 = sp0 (slot 2); x9 = s1 = sp1;
   x22 = s6 = SB + F/8 (slot 88). The others are dead: fresh slots from RT_XN. *)
Definition rt_X_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition rt_X_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition RT_XN : nat := 600.
Definition rt_X_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 88 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* The save area, as the prologue writes it (0x7eed8-0x7ef08, sp = sp0 - 192): s11 at sp0-104 .. ra at sp0-8. *)
Definition rt_X_saves : list YP09.chunk :=
[ YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
(* The facts every state of the walk carries (S0's ss_H, same order as the donor's): 88 = SB + F/8, 87 = the flag address,
   75 = F, 70 = sp1, 2 = sp0, 11 = n, 32 = SB; alias SB + (F >> 3) = slot 88. *)
Definition rt_X_atoms : list (nat * afact) :=
[ (88%nat, mkAF (SB + 512) (SB + 2 ^ 44) 2); (87%nat, HPTR 0); (75%nat, HPTR 5); (70%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
  (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition rt_X_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)].
(* Regions: the frame header F[0,32) (written: F[0]); the frame's shadow (read-only here, made writable by fs_rwF);
   the flag slot F[112,128) with the flag address at F+120; the spills 16(s1) = 24(s1) = F (read-only); the save area. *)
Definition ss_X_0 : sstate :=
mkSS 0x7f274 rt_X_regs
[ YP09.mkRegion (Some 75%nat) 0 32 0 32 [];
  YP09.mkRegion (Some 88%nat) 0 16 0 0 [];
  YP09.mkRegion (Some 75%nat) 112 128 112 128 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))];
  YP09.mkRegion (Some 70%nat) 16 32 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 75 0)); YP09.mkChunk 24 (CVal 8 (SOff 75 0))];
  YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 rt_X_saves ]
None (mkFacts rt_X_atoms [] rt_X_alias).
Definition ss_X : sstate := Eval vm_compute in ss_havoc_regs ss_X_0 RT_XN rt_X_deads.
(* [A/ACf7.v:51-56] *)
Definition INV_XP (B : asyms) (MT : ameter_ops) (PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= EV_LIB /\ acc <= c_T cx /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\ PX ly3 (ablocks B ly3 S3) W3 (ms_mem ms3) md3.
Definition INV_X (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx => INV_XP B MT (fun _ _ _ _ _ => True) cx.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Variable PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis PXK : forall ly bl (W : world tfibsegs) (m m' : word -> option byte) (md : Model) mat,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
PX ly bl W m md -> PX ly bl W m' (with_vm_backing (m_vm_lazy md) mat md).
(* [A/ACf4.v:46-61]: add the one-byte region of the flag (slot 87) to the state. Changes: tfibsegs; no unfold of the
   constant-address regions (ss_X has none). *)
Ltac add_flag_regionRT HS AG E87 Hp HFLrng HFLown HnoF :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoF fl); [lia | exact HFLown] | match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* [A/ACf4.v:62-77]: every writable byte of the run's state is the frame's, its shadow's, the stack's or the flag.
   Changes: class 1 (exists 1, fs_frame_bytes 1 = 128, / 8 = 16). *)
Ltac wrangeRT AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lazymatch goal with FFS : LLVMF_STK = _ |- _ => clear - Hr FFS; lia end
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeRT" ]
| ]);
destruct Hin.
(* [A/ACf4.v:78-117] *)
Lemma rt_XP_aux : True -> rt_from B MT FP (rt_postP B MT FP PX) ss_X (INV_XP B MT PX).
Proof.
intros _. rt_prelude.
pose proof HINV as (Hk3 & Hacc & HPerm3 & HPX). cbn [c_ly c_S] in HPerm3. cbn [c_T] in Hacc.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJ3) Hfin3) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
fs_rwF HS E88 HFSpres3.
add_flag_regionRT HS AG E87 HFLpres' HFLrng' HFLown' HnoF.
aj_run_flag_sh tfibtbl_lib_ok HS HJ3; [clear; lia | wrangeRT AG fpos F EFA3 EFL3 | flag0 E87 EFL3 |].
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rt_postP. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ ?kx =>
lazymatch goal with |- exists ly' S' regs' mem' md' k', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx, kx end end.
split.
{ unfold cfg_at. rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 1%nat) by lia.
rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra1. unfold raZ in Hra. unfold w64. rewrite <- Hra, Z_to_bv_bv_unsigned. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs _ LAWS tfib_segs_low); exact HJ3|].
split; [exact Hk3|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [rewrite Ra0; reflexivity|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); exact HPerm3|].
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact (mo_le_mono MT MTL _ _ _ _ HMLE Hacc)|].
(* PX [A/ACf4.v:104-116]: the run wrote only the frame, its shadow, the flag byte and the stack, none of them an image byte.
   tfib_img_range's bounds and off_img are named (TFIB_IMG_LO / TFIB_IMG_END = YImgTop.IMG_LO / IMG_TOP); unfolded here. *)
lazymatch goal with HFrx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ ?m1) |- _ =>
unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3);
eapply PXK; [| first [exact HPX | eapply PXK; [intros; reflexivity | exact HPX]]];
intros a Ha; apply aview_eq_of; apply HFrx;
pose proof (tfib_img_range a Ha) as Har; unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in Har;
rewrite unsigned_lit_small by (clear - Har; lia);
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [ clear - Hrg Har Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img HFLrng'; unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia
| match goal with |- ?g => idtac "PXK-FAIL" g end ]
|]);
destruct Hin end.
Qed.
Lemma rt_XP : rt_from B MT FP (rt_postP B MT FP PX) ss_X (INV_XP B MT PX).
Proof. exact (rt_XP_aux I). Qed.
End c.
(* [A/ACf4.v:121-127]; knock's rt_post has PX = True (APgCtx.signature.v D5), so PXK holds trivially. *)
Lemma rt_X (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) :
ameter_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) -> astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
ameter_fs_laws MT -> rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT).
Proof.
intros MTL TL LAWS ML ASF FFL MTF.
exact (rt_XP B MT MTL FP TL LAWS ML ASF FFL MTF (fun _ _ _ _ _ => True) ltac:(intros; exact I)).
Qed.
End b.
