(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24: no function proved here alone; this is segment S0 of LLVMFuzzerTestOneInput's walk, whose top claim is
   lib/A/PPgMain.v.

   SEGMENT S0 ENTRY, pc 0x806b4 .. 0x807cc, ending at ss_H (0x807d0, lib/A/PPgMainSt.v). Every address was read from
   the pinned image bytes with capstone 5.0.7. The walk, with knock's line it follows:
   - 0x806b4-0x806f4: the 128-byte save frame (13 saves at [sp0-104, sp0)), s0 = sp0, `andi sp,sp,-0x20`; the first
     run stops at 0x806f8 (knock 0x7ef14); sp1 := 32 * ((sp0 - 128) / 32) into env slot 70 (knock -192).
   - the stack region is trimmed to the saves [sp0-104, sp0) (as knock), and region 70 = [s1+16, s1+24) is added
     for the one spill `sd s8,0x10(s1)` at 0x80758 (knock [16,88)).
   - 0x806f8-0x80724: the two GOT loads (0x99050 shadow base, 0x990a8 use-after-return option), s6 := SB, the
     option test `beqz a2` at 0x8071c decided by the option cell's SLit 1, a0 := 0x60, `jal 3ca58` at 0x80724
     (__asan_stack_malloc_1, class 1); the run stops at 0x3ca58 by SR_fetch.
   - the side-stack call through aj_stack_malloc_atS (lib/A/PPgMainCall.v) with class 1 and ASM1; its premise
     count_cid 1 (frames S) < fs_frames 1 is the call-site lemma pin_fs1_site.
   - the class-1 frame facts (F = frame_addr ly 1 fpos, 128 bytes, 16 shadow bytes, the flag address at F + 120),
     the atoms 75 / 87 / 88 and the alias SB + (F >> 3) = slot 88, as knock.
   - 0x80728-0x807c8: `bnez s2` decided by HPTR 5 on F (the real-stack path 0x8073c-0x80754 is never reached),
     `sd s8,0x10(s1)`, the frame header F[0..24) = 0x41B58AB3 / 0x1ffeb / 0x806b4, the 12 shadow bytes
     f1 x4, f8, f2 x3, f8, f3 x3 (0x80794-0x807c8).
   - 0x807cc `bnez a0` with a0 = n >> 26: split with SRr_sym_branch; the taken side (-> 0x80940) is refuted by
     n < 2 ^ 26 (atom 11); the fall-through runs to 0x807d0.
   - the join into ss_H (window 400) and the hand-off to the rest of the walk (RB).
   Section hypotheses: MTL TL LAWS ML ASM1 SMP FFL MTF and RB : rt_from B MT FP POST ss_H (INV_0 B MT 0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgMain0.v, with its module paths, module names and numbers changed; 913 of its 982 lines of code are new or changed and 218 lines of the source are left out. *)
(* diginet_ring_encode at image B 0x85c1c, 183 instructions, against its B contract cdcU_ring_specX
   (lib/AU/Prog/CPgEncU.v). Real frame 96 and sp realigned to 32 (atom 70 = sp1); the class-0 side-stack frame F
   (atom 75, its flag address atom 87, its shadow SB + F / 8 atom 88) taken at 0x85c8c; the alignment test of p
   (0x85d28, the UBSan trap 0x85ec8 not taken: p mod 8 = 0, atom 10's fact with al2 = 3); the checks of p + 17 and
   p + 16 (the personality bytes, read-only region on atom 10); the seven loop iterations; the three payload bytes
   in F + 32 .. F + 34 with their shadow byte 3; diginet_sysex_encode at 0x85df0 through its contract; the alignment
   test of out (0x85dfc, the trap not taken: out mod 4 = 0, atom 13's fact with al2 = 2); the key store at out + 28;
   every path to 0x85e30 and the exit there (diginet_ring_encode_B_2.v). The token engine runs the checks with the
   frame's shadow region dropped (its window lies in the shadow band); the region is added back for the walk's
   stores into it (0x85db8, 0x85e2c) and for the exit. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YC85 YCeo YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCbqU YImgTopU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkKeptU CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_ring_encode_B_1 diginet_ring_encode_B_kit diginet_ring_encode_B_2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a region of the walk kept across the frame request: its bytes off the runtime's own and off the request's
   stack, its window present *)
Lemma rgb_region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
(* the classification of a run's write windows into the window and the walk's frame zone *)
Ltac rgb_wzc AG :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb);
lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb;
    rewrite ?unsigned_lit_small in Hb by (unfold shadow_addr, SHADOW_OFF in *; lia);
    unfold rgb_wz, frame_rng, in_zr; cbn [fst snd]; try change (fs_frame_bytes 0 / 8) with 8; try change (fs_frame_bytes 0) with 64;
    repeat match goal with Fd := frame_addr _ _ _ |- _ => progress fold Fd end;
    first [ left; unfold TB_ring, TB_sysex, ESTACK; lia | right; left; lia | right; right; lia
          | let t := type of Hb in match goal with |- ?g => fail 4 "rgb_wzc: a write window off the window and the frame:" t g end ]
  | ]); destruct Hr.
Ltac rgb_wzc0 AG :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb);
lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb;
    unfold TB_ring, TB_sysex, ESTACK; lia
  | ]); destruct Hr.
(* a run's frame as a kept fact *)
Ltac rgb_frx HFr :=
idtac; let a := fresh "a" in let Ha := fresh "Ha" in let Hx := fresh "Hx" in
intros a Ha Hx; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
rewrite unsigned_lit_small by exact Ha; exact Hx.
(* the walk's kept invariant through the last run, whose windows lie in the window or in the walk's own frame *)
Ltac rgb_kt AG HJ0 HJ2c HPm :=
lazymatch goal with
| HFr : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG : mem_grows _ _,
  KT : tcj_kept tfibsegs ?Bv TB_ring ?lyc ?Sc ?W ?memc ?W1 ?m1 ?sp ?E0,
  L : AR_laws tfibsegs ?Bv, FF : frame_flag_lawP tfibsegs ?Bv |- _ =>
  let KT1 := fresh "KT" in
  pose proof (rgb_kt_run Bv L FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp E0 (in_wrange Ev rs) W1 m1 m2 HJ0 HJ2c HPm
    ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia) KT ltac:(rgb_frx HFr) ltac:(rgb_wzc AG)
    ltac:(idtac; let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp])) as KT1;
  clear KT HFr HG; rename KT1 into KT
end; clear_frames.
(* a value of memory off every write window of the last run, carried through it *)
Ltac rgb_carry AG HFr V :=
lazymatch type of HFr with frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2) =>
lazymatch type of V with val_mem _ (mrestrict _ m1) ?a ?n ?v =>
  let V2 := fresh "V" in
  assert (V2 : val_mem tfibsegs (mrestrict H m2) a n v);
  [ apply (cw_val_mem_kept H H m1 m2 a n v); [|exact V];
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
    unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 x)); [reflexivity|];
    rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia);
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
    intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb;
        rewrite ?unsigned_lit_small in Hb by (unfold shadow_addr, SHADOW_OFF in *; lia);
        unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; lia
      | ]); destruct Hr
  | clear V; rename V2 into V ] end end.
(* a value of memory carried through a runtime call's kept fact HK *)
Ltac rgb_carry_k HK V :=
lazymatch type of V with val_mem _ (mrestrict ?H ?m1) ?a ?n ?v =>
lazymatch type of HK with forall x, _ -> _ -> _ -> aview _ _ ?m2 x = _ =>
  let V2 := fresh "V" in
  assert (V2 : val_mem tfibsegs (mrestrict H m2) a n v);
  [ apply (cw_val_mem_kept H H m1 m2 a n v); [|exact V];
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
    apply HK; unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, TB_ring, TB_sysex, ESTACK in *; lia
  | clear V; rename V2 into V ] end end.
(* the values off the runtime's own through the last run (before rgb_kt, which clears the run's frame) *)
Ltac rgb_ka AG HAR HAR2 Hfin2 Hnin :=
lazymatch goal with
| HFr : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), KA : rgb_ka ?Bv ?lyc ?Sc ?sp ?H ?m1 ?m0 |- _ =>
  lazymatch type of Hfin2 with In (0, ?pos) _ =>
  let KA1 := fresh "KA" in
  pose proof (rgb_ka_run Bv _ _ _ _ _ _ _ _ _ pos sp (in_wrange Ev rs) H m1 m2 m0 HAR HAR2 Hfin2 Hnin KA
    ltac:(rgb_frx HFr) ltac:(rgb_wzc AG)) as KA1;
  clear KA; rename KA1 into KA end
end.
(* the write windows of the key-store run: the command's last word (atom 13) in front, then the walk's own *)
Ltac rgb_awr13 AG sp sp1 pos E13 Hotw HPm4 Efa4 :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (YCbq.awr_ok E rs' stk sp0 fp b0 bc ly own) end;
eapply YCbq.awr_ok_cons_gen;
[ reflexivity
| lazymatch goal with |- bv_unsigned (ew ?Ev 13) = _ => rewrite (E13 Ev AG); apply unsigned_lit_small; lia end
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  let Haw := fresh "Haw" in destruct (Hotw a ltac:(lia)) as (Haw & _);
  apply (rgb_awr_byte_mono _ _ _ _ _ _ _ _ _ _ _ Haw);
  [ let bb := fresh "bb" in let mm := fresh "mm" in let Hin := fresh "Hin" in
    intros bb mm Hin; exact (Permutation_in _ (Permutation_sym HPm4) Hin) | apply incl_tl, incl_refl | exact Efa4 ]
| rgb_awr AG sp sp1 pos ].
(* at 0x85e30: join the state to ss_rgX and close by rgb_exit, the result v in a0 *)
Ltac rgb_exit_tac HS Hsp1 HJ Hnin HPm HSt HAR Hotd :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
  let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10;
  rgb_join HS;
  lazymatch type of HS with st_ok _ ?E3 _ _ =>
    let Ex := fresh "Ex" in let HEx := fresh "HEx" in remember E3 as Ex eqn:HEx in HS;
    lazymatch goal with
    | E70 : ew ?Eo 70 = _, E75 : ew ?Eo 75 = _, E87 : ew ?Eo 87 = _, E88 : ew ?Eo 88 = _,
      HAE : env_agree 32 _ ?Eo, HSB : shadow_addr _ = SB + _ / 8,
      L : AR_laws tfibsegs ?Bv, MLx : model_laws _, ASFx : astack_free_law _ _, FFLx : frame_flag_lawP _ _,
      MTFx : ameter_fs_laws ?MTv |- _ =>
      eapply (rgb_exit Bv MTv L MLx ASFx FFLx MTFx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ex);
      [ eassumption | exact Hsp1 | exact HJ | exact Hnin | exact HPm
      | exact HSt | cw_io
      | rewrite HEx; apply env_agree_havoc_ge; [lia | exact HAE]
      | rewrite HEx, ew_havoc_old by lia; exact E70
      | rewrite HEx, ew_havoc_old by lia; exact E75
      | rewrite HEx, ew_havoc_old by lia; exact E87
      | rewrite HEx, ew_havoc_old by lia; rewrite E88, HSB; reflexivity
      | rewrite HEx; change 600%nat with (600 + 0)%nat; rewrite (ew_havoc_new _ 600 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth ms_regs restrict mkst];
        rewrite R10; first [apply bv_eq; reflexivity | cbn [fst]; assumption]
      | exact Hotd
      | lazymatch goal with L : AR_laws _ _ |- _ => pose proof (rgb_tdst_below _ L _ _ _ _ _ _ 32 HAR Hotd ltac:(lia)) end;
        unfold TB_ring, TB_sysex, ESTACK in *; lia
      | idtac
      | idtac
      | idtac
      | exact HS ]
    end
  end
end.
(* the state re-seated at the return address of a call (ACep.reseat) with env_agree 32 carried *)
Ltac rgb_reseat HS HJ2 HP2 keep AG HAE kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rgb_rebase HS AG HAE.


(* the one byte a 1-byte chunk of a region holds *)
Lemma rgb_byte_of_region : forall E m n b lo hi wlo whi cs od e v,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> U E e mod 256 = v ->
val_mem tfibsegs m (b + od) 1 v /\ 0 <= v < 256.
Proof.
intros E m n b lo hi wlo whi cs od e v HR Hb Hin Hv.
pose proof (field_of_region_any E m n b cs lo hi wlo whi od 1 e HR Hb Hin ltac:(cbn; lia)) as HV.
change (N.to_nat 1) with 1%nat in HV. change (8 * Z.of_N 1) with 8 in HV.
change (2 ^ 8) with 256 in HV. unfold U in Hv. rewrite Hv in HV.
split; [exact HV|]. rewrite <- Hv. apply Z.mod_pos_bound. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the frame's 8 shadow bytes (atom 88) back as a writable region in front, from the frame facts of the
   journal HJx's state *)
Ltac rgb_add88 HJx Hfinx Efax AG E10x :=
let HFbx := fresh "HFb" in let HFsx := fresh "HFs" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 _ (proj1 HJx) Hfinx) as (_ & _ & HFbx & HFsx);
try rewrite Efax in HFbx, HFsx; change (fs_frame_bytes 0) with 64 in HFbx, HFsx; change (64 / 8) with 8 in HFsx;
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
lazymatch goal with E88 : ew _ 88 = _ |- _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 88%nat) 0 8 0 8 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite E88, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia);
        split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (HFsx o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    try rewrite (E10x Ev AG); evalE AG; rewrite ?unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia);
    unfold shadow_addr, SHADOW_OFF, YCbq.off_img, YCbqU.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg,
      TFIB_IMG_LO, TFIB_IMG_END, TB_ring, TB_sysex, ESTACK in *;
    repeat split; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end;
clear HFbx HFsx.
(* the same for the frame (75, the flag address at F + 56) *)
Ltac rgb_add75 HJx Hfinx Efax AG V56x E10x :=
let HFbx := fresh "HFb" in let HFsx := fresh "HFs" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 _ (proj1 HJx) Hfinx) as (_ & _ & HFbx & HFsx);
try rewrite Efax in HFbx, HFsx; change (fs_frame_bytes 0) with 64 in HFbx, HFsx; change (64 / 8) with 8 in HFsx;
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
lazymatch goal with E75 : ew _ 75 = Z_to_bv 64 ?Fv, E87 : ew _ 87 = Z_to_bv 64 ?FLv |- _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_frame_region 75 87 0) HS eq_refl
  ltac:(unfold region_ok, cw_frame_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        change (fs_frame_bytes 0) with 64; rewrite E75, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (HFbx (Fv + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val tfibsegs Ev _ Fv 56 8 (SOff 87 0) FLv);
          first [ (cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) | exact V56x | zside
                | (cbn; unfold TB_ring, TB_sysex, ESTACK in *; lia) ] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, cw_frame_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0) with 64; try rewrite (E10x Ev AG); evalE AG; rewrite ?unsigned_lit_small by lia;
    unfold YCbq.off_img, YCbqU.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, TFIB_IMG_LO, TFIB_IMG_END, TB_ring, TB_sysex, ESTACK in *;
    repeat split; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end;
clear HFbx HFsx.
(* the frame's shadow region (in front) dropped before a run of the token engine *)
Ltac rgb_drop88 :=
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let rs := eval vm_compute in (tl (ss_mem ssv)) in
  pose proof (st_ok_submem tfibsegs Ev ssv msv rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.

Section e.
Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.
Hypothesis SYSEX : cdcU_sysex_specX tfibsegs B MT 0x85174.

Lemma rgb_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip mask out : Z) (before : list Z),
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_ring ->
getr regs 10 = w64 p -> pers_argA tfibsegs B W memc (spZ regs) TB_ring p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) strip -> arg_zxA 16 (getr regs 12) mask ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_ring out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj pd p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr tfibsegs W (cfg_at tfibsegs 0x85c1c regs memc mdc)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs TB_ring (cenc_wr out) lyc Sc W memc mdc
  (cenc_res tfibsegs out before (ring_spec pd strip mask))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip mask out before
HE H10 HPA Hp8 H11 H12 H13 Ho4 HOUT HOOB HPD HFR.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_ring HE
  ltac:(unfold TB_ring, TB_sysex, ESTACK; lia)) as (Hceil0 & H47 & H46 & _ & Hpres0).
unfold TB_ring, TB_sysex, ESTACK in Hwlo, Hceil0, H46, Hpres0.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47' & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kc & Ku & Kg & Kgu).
rewrite HBgot, HBcell in Kg. rewrite HBcell in Kc. rewrite HBguar, HBuar in Kgu. rewrite HBuar in Ku.
pose proof (val_mem_of_rdword tfibsegs _ _ _ _ Kgu) as Kguar.
pose proof (val_mem_of_rd32 tfibsegs _ _ _ _ Ku) as Kuar.
clear Kc Ku Kg Kgu.
set (sp := spZ regs) in *.
pose proof HOUT as ((Hout0 & Hout1 & Hotd & Hotw & Hora & Hohull & Hoam & Howin) & HGbef & HLbef).
destruct H11 as (Hstrip32 & H11). destruct H12 as (Hmask16 & H12).
assert (Hprng : 0 <= p <= 2 ^ 63 - 20) by (destruct pd as [d|]; [destruct HPA as (? & ? & _); lia | cbn in HPA; lia]).
(* the walk's kept invariant (write set: none until the call of sysex) and the values off the runtime's own *)
assert (KT : tcj_kept tfibsegs B TB_ring lyc Sc W memc W memc sp (fun _ => False))
  by (apply (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp TB_ring _ HJ0);
      unfold TB_ring, TB_sysex, ESTACK; lia).
assert (KA : rgb_ka B lyc Sc sp (w_H W) memc memc) by (intros a _ _; reflexivity).
(* atom 10 (p) 8-aligned and atom 13 (out) 4-aligned, so the engine decides the two UBSan alignment tests *)
assert (HS : st_ok tfibsegs (Ereg regs (cw_extra []))
  (mkSS 0x85c1c sr_atoms (cw_regs 96 ++ [uar_got_region; uar_cell_region]) None
   (mkFacts (cw_atoms ++ [(10%nat, mkAF 0 (2 ^ 63 - 20) 3); (13%nat, mkAF 1 (2 ^ 63) 2)]) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x85c1c) memc (seg_rom tfibsegs)))).
{ apply (cw_entry B TL LAWS 0x85c1c 96 [] [uar_got_region; uar_cell_region]
    [(10%nat, mkAF 0 (2 ^ 63 - 20) 3); (13%nat, mkAF 1 (2 ^ 63) 2)] lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(fold sp; lia) Hal16
    ltac:(intros a Ha; apply Hpres0; fold sp in Ha; lia) ltac:(vm_compute; reflexivity)).
  - unfold uar_got_region, uar_cell_region. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_GOT_uar 8 (SLit A_uar_glob) A_uar_glob);
      [reflexivity | unfold A_uar_glob; zside | zside |]. rewrite Z.add_0_l. exact Kguar.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_uar_glob 4 (SLit 1) 1);
      [reflexivity | zside | zside |]. rewrite Z.add_0_l. exact Kuar.
  - apply pairwise_disjoint_of_extents.
    unfold cw_regs, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with sp.
    unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), (ew_Ereg_nat regs _ 13 13%bv eq_refl), H10, H13.
    unfold w64. rewrite !unsigned_lit_small by lia. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
    repeat split; try lia; exact I. }
clear Kguar Kuar.
remember (Ereg regs (cw_extra [])) as E eqn:HE0.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (B2 : bv_unsigned (ew E 2) = sp) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE0.
rgb_shok0.
unfold cfg_at. change (w64 0x85c1c) with (Z_to_bv 64 0x85c1c).
(* 0x85c1c-0x85c54: the saves, s0 = sp, andi sp,sp,-32 *)
cw_run_to cw_awr_stk 0x85c58.
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ memc) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  pose proof (cw_kept_step B LAWS TB_ring lyc Sc W memc mdc W memc m2 sp _ (in_wrange Ev rs)
    ltac:(unfold TB_ring, TB_sysex, ESTACK; lia) HAR KT ltac:(rgb_frx HFr)
    ltac:(idtac; let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; left; revert a Hx; rgb_wzc0 AG)
    ltac:(idtac; let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp])) as KT1;
  pose proof (rgb_ka_run0 B lyc Sc sp (in_wrange Ev rs) (w_H W) memc m2 memc KA ltac:(rgb_frx HFr) ltac:(rgb_wzc0 AG)) as KA1;
  clear KT KA; rename KT1 into KT; rename KA1 into KA end.
clear_frames.
set (sp1 := 32 * ((sp + -96) / 32)).
destruct (sp1_facts (sp + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : sp - 112 <= sp1 <= sp - 96) by lia. clear Hsp1r.
assert (Ew2 : ew E 2 = Z_to_bv 64 sp) by (rewrite (EE 2%nat 2%bv eq_refl); unfold sp, spZ; symmetry; apply Z_to_bv_bv_unsigned).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (rgb_denot_and_m32 Ev 2 sp (-96) Ew2 ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 70 Ev (havoc Ev 70 [Z_to_bv 64 sp1]) ssv msv HS
(env_agree_havoc_ge 70 70 Ev Ev _ ltac:(lia) (env_agree_refl 70 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ (havoc ?Ev _ _) _ _ =>
assert (E70 : ew (havoc Ev 70 [Z_to_bv 64 sp1]) 70 = Z_to_bv 64 sp1) by exact (ew_havoc_new Ev 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
rgb_rebase HS AG HAE.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
trim_base HS 2%nat (-88) 0.
(* region 70: the spill 0(s1) .. 8(s1) *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E70, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs);
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let HJp := fresh "HJp" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _); apply HJp; lia end)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E70, (AG 2%nat) by lia; rewrite B2, unsigned_lit_small by lia;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x85c58-0x85c8c: the GOT loads, the use-after-return test (decided), a0 = 64, jal frame_alloc_0 *)
rgb_shok0. cw_run ltac:(rgb_awr AG sp sp1 0).
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  pose proof (cw_kept_step B LAWS TB_ring lyc Sc W memc mdc W m1 m2 sp _ (in_wrange Ev rs)
    ltac:(unfold TB_ring, TB_sysex, ESTACK; lia) HAR KT ltac:(rgb_frx HFr)
    ltac:(idtac; let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; left; revert a Hx; rgb_wzc0 AG)
    ltac:(idtac; let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp])) as KT1;
  pose proof (rgb_ka_run0 B lyc Sc sp (in_wrange Ev rs) (w_H W) m1 m2 memc KA ltac:(rgb_frx HFr) ltac:(rgb_wzc0 AG)) as KA1;
  clear KT KA; rename KT1 into KT; rename KA1 into KA end.
clear_frames.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250444 with (pc_stack_malloc (as_code B) 0) by (rewrite HBcode; reflexivity).
pose proof (rgb_count_cid_le 0 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msY)
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - change (fs_frames 0) with 16384. lia. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJt2 & HKA & HIO2).
rewrite Hes in HK, HKA. replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK, HKA by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in HK, HKA by lia.
lazymatch type of HK with acall_kept _ _ _ _ _ ?m1 _ _ _ _ _ =>
  pose proof (cw_kept_call B TB_ring lyc Sc W memc W m1 mem2 sp (sp1 - 4096) sp1 _
    ltac:(unfold TB_ring, TB_sysex, ESTACK; lia) ltac:(lia) ltac:(unfold TB_ring, TB_sysex, ESTACK; lia) ltac:(lia) KT HK) as KT1;
  assert (KA1 : rgb_ka B lyc Sc sp (w_H W) mem2 memc)
    by (intros a Ha Hn; rewrite (HKA a Ha); [exact (KA a Ha Hn) | intros X; exact (Hn (or_introl X)) |
        intros X; apply Hn; right; unfold TB_ring, TB_sysex, ESTACK; lia]);
  clear KT KA; rename KT1 into KT; rename KA1 into KA end.
pose proof HK as (K1 & _).
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp2 & _).
clear HJ. rename HJ2 into HJ.
rgb_reseat HS HJ HP2 [0; 1; 2; 3; 4; 5]%nat AG HAE
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some _) _ _ _ _ _) =>
  eapply rgb_region_kept_eq; [ evalE AG | intros a Ha; apply K1; lia | intros a Ha; apply HJp2; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot0 | exact Kgot2 | clear; lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell0 | exact Kcell2 | clear; lia]
  | change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar0 | exact Kguar2 | clear; lia]
  | change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar0 | exact Kuar2 | clear; lia] ] end ]).
clear K1 HK HKA HJp2 Kgot0 Kcell0 Kguar0 Kuar0 Kgot2 Kcell2 Kguar2 Kuar2.
(* the class-0 frame F (64 bytes, 8 shadow bytes, the flag address at F + 56) *)
pose proof (proj1 HJ) as HAR2.
assert (Hfin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
destruct (frame_al64 tfibsegs B _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in HF4096, HFceil, HFapp, HFimg.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
rreg HS (10%bv : bv 5) RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
clear Ha0.
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite (Z.div_mod F 64) at 1 by lia. rewrite HF64, Z.add_0_r.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8hi : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold TB_ring, TB_sysex, ESTACK in *; lia).
assert (HSB : shadow_addr F = SB + F / 8) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) ssv msv HS
(env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
assert (E87 : ew (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) 87 = Z_to_bv 64 FL)
  by exact (ew_havoc_new Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 0 (Z_to_bv 64 0) ltac:(cbn; lia));
assert (E88 : ew (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) 88 = Z_to_bv 64 (shadow_addr F))
  by exact (ew_havoc_new Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
clear HS. rename HS3 into HS. pose proof HJ as HJ2c.
rgb_rebase HS AG HAE.
rename RF into E75.
pose proof (cw_frame_afacts B LAWS _ 75 87 88 lyc S2 W mem2 md2 0 pos FFL HAR2 Hfin2 E75 E87 E88) as (AF75 & AF87 & AF88).
assert (E32' : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 32 = Z_to_bv 64 SB)
  by (intros Ev AGv; rewrite (AGv 32%nat) by lia; exact E32).
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ 75 (HPTR 6) HS AF75) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 87 (HPTR 0) HS AF87) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS AF88) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias tfibsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB E75 ltac:(lia) (E32' Ev AG)
  ltac:(rewrite E88, HSB; reflexivity))) as HS3; clear HS; rename HS3 into HS end.
clear AF75 AF87 AF88.
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (_ & _ & _ & (HFLg0 & _ & HFLgc)).
(* region 75 = the frame (the flag address at F + 56), then region 88 = its 8 shadow bytes (zero after the request) in front *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_frame_region 75 87 0) HS eq_refl
  (cw_frame_region_ok B LAWS FFL Ev 75 87 lyc S2 W mem2 md2 0 pos HAR2 Hfin2 E75 E87 Hflag)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, cw_frame_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0) with 64; change (fs_frame_bytes 0 / 8) with 8; evalE AG; rewrite ?HSB;
    unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
    unfold YCbq.off_img, YCbqU.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg in *;
    rewrite ?unsigned_lit_small by lia; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_fshadow_region 88 0) HS eq_refl
  (cw_fshadow_region_ok B LAWS Ev 88 lyc S2 W mem2 md2 0 pos HAR2 Hfin2 E88 Hz)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, cw_fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0 / 8) with 8; evalE AG; rewrite HSB;
    unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
    unfold YCbq.off_img, YCbqU.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg in *;
    rewrite ?unsigned_lit_small by lia; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
assert (HPm : Permutation (ablocks B lyc S2) (ablocks B lyc Sc)) by (rewrite Eab; apply Permutation_refl).
pose proof (proj2 (cw_frame_start MT MTL MTF B lyc Sc S2 HJt2)) as HM2.
assert (HF8c : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia).
(* the command at out lies off the window and off the walk's own frame and its shadow *)
assert (Hout_nz : forall a, out <= a < out + 32 -> ~ rgb_wz sp lyc pos a).
{ intros a Ha [Hw | [Hf | Hs]].
  - pose proof (rgb_tdst_below B LAWS lyc Sc W memc mdc out 32 HAR Hotd ltac:(lia)). unfold TB_ring, TB_sysex, ESTACK in *. lia.
  - destruct (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem2 md2 k 0 pos a HJ0 HJ2c HPm (or_introl Hf))
      as (_ & _ & Hb & Hfr).
    destruct (Hotd a Ha) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)];
    [ exact (Hb bb mm (a - bb) Hin ltac:(lia) ltac:(lia)) | exact (proj1 (Hfr cid ps Hin) Hr) ].
  - unfold in_zr in Hs. cbn [fst snd] in Hs. change (fs_frame_bytes 0 / 8) with 8 in Hs.
    change (frame_addr lyc 0 pos) with F in Hs.
    unfold amem_range, shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
(* 0x85c90-0x85d20: bnez s2 (decided, F >= 4096), the spill, the frame header, the shadow map, a0 = -1, to beqz s6 (p) *)
aj_run_sh tfibtbl_lib_ok HS HJ; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ.
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  pose proof (rgb_kt_run B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem2 md2 k pos sp _
    (in_wrange Ev rs) W m1 m2 HJ0 HJ2c HPm ltac:(unfold TB_ring, TB_sysex, ESTACK; lia) KT ltac:(rgb_frx HFr) ltac:(rgb_wzc AG)
    ltac:(idtac; let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp])) as KT1;
  pose proof (rgb_ka_run B lyc Sc W memc mdc S2 W mem2 md2 pos sp (in_wrange Ev rs) (w_H W) m1 m2 memc HAR HAR2 Hfin2 Hnin KA
    ltac:(rgb_frx HFr) ltac:(rgb_wzc AG)) as KA1;
  clear KT KA; rename KT1 into KT; rename KA1 into KA end.
clear_frames.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
apply (SRr_sym_branch tfibsegs Wg Ev ssv msF mdF _ BC_EQ (SOff 10 0) (SLit 0) HS) end end;
clear HS; intros Hc HS.
- (* taken: p = 0, so pd = None; a0 = -1 *)
  assert (Hp0 : p = 0).
  { destruct pd as [d|]; [|exact HPA]. exfalso. destruct HPA as (Hp0 & Hp63 & _).
    rewrite branch_eq_U in Hc. rewrite (cw_U_atom0 _ 10 p ltac:(rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity) ltac:(lia)) in Hc.
    rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
  destruct pd as [d|]; [exfalso; destruct HPA as (HPA & _); lia|].
  change (ring_spec None strip mask) with (E_ARG, @None cmd).
  aj_run_to_sh tfibtbl_lib_ok HS HJ 0x85e30; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ.
  rgb_kt AG HJ0 HJ2c HPm.
  rgb_exit_tac HS Hsp1 HJ Hnin HPm HM2 HAR Hotd.
  + exact (rgb_tcj_mono B _ _ _ _ _ _ _ _ (fun _ => False) _ (fun a H => False_ind _ H) KT).
  + cbn [snd cmd_outZ]. eapply rgb_garr8_kept; [rewrite HLbef; exact Hotd | exact KT | exact HGbef].
  + exact HLbef.
- (* not taken: p <> 0, so pd = Some d *)
  destruct pd as [d|].
  2: { exfalso. cbn [pers_argA] in HPA. rewrite branch_eq_U in Hc.
       rewrite (cw_U_atom0 _ 10 p ltac:(rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity) ltac:(lia)) in Hc.
       rewrite U_lit in Hc by lia. subst p. rewrite Z.eqb_refl in Hc. discriminate Hc. }
  pose proof HPA as (Hp0 & Hp63 & Hdev & Hstr & Hch & Hctr & HGp & HPimg).
  assert (E10 : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 10 = Z_to_bv 64 p)
    by (intros Ev AGv; rewrite (AGv 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity).
  assert (E13 : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 13 = Z_to_bv 64 out)
    by (intros Ev AGv; rewrite (AGv 13%nat) by lia; rewrite (EE 13%nat 13%bv eq_refl), H13; reflexivity).
  assert (E11 : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 11 = Z_to_bv 64 (s32 strip))
    by (intros Ev AGv; rewrite (AGv 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl), H11; reflexivity).
  assert (E12 : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 12 = Z_to_bv 64 mask)
    by (intros Ev AGv; rewrite (AGv 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl), H12; reflexivity).
  (* the frame's flag address, read from region 75 before the shadow region goes *)
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_region_nth Ev ssv msv 1 _ HS eq_refl) as R75;
    cbn [ms_mem restrict mkst] in R75;
    pose proof (field_of_region Ev _ 75 F _ _ _ _ _ 56 8 _ FL R75 ltac:(rewrite E75; apply unsigned_lit_small; lia)
      ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (_ & _ & _ & (HFL0 & _ & HFLc)); cbn; unfold TB_ring, TB_sysex, ESTACK in *; lia) ltac:(cbn; lia)) as V56;
    clear R75 end.
  (* the token engine runs the checks: drop the writable shadow region 88 and the image cells; keep 75, 70, 2 *)
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    let rs := eval vm_compute in (firstn 3 (tl (ss_mem ssv))) in
    pose proof (st_ok_submem tfibsegs Ev ssv msv rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end.
  norm_ss HS.
  (* the personality bytes p + 16 (device, atom 89) and p + 17 (strips, atom 90), read-only, on atom 10 *)
  pose proof HPimg as (Hpi0 & _ & Hpi63 & Hpiam & Hpiwin & Hpist & Hpius).
  pose proof (tfib_img_range (p + 16) (proj1 (Hpist (p + 16) ltac:(lia)))) as Hpr0.
  pose proof (tfib_img_range (p + 19) (proj1 (Hpist (p + 19) ltac:(lia)))) as Hpr3.
  lazymatch type of KA with rgb_ka _ _ _ _ _ ?mk _ =>
  assert (VP : forall j, (j < 4)%nat -> val_mem tfibsegs (mrestrict (w_H W) mk) (p + 16 + Z.of_nat j) 1
      (nth j [d_dev d; d_strips d; d_chars d; d_counter d] 0));
  [ intros j Hj; apply (cw_val_mem_kept (w_H W) (w_H W) memc mk _ 1 _); [|exact (proj1 (HGp j ltac:(cbn; lia)))];
    intros x Hx; change (Z.of_nat 1) with 1 in Hx; apply KA; [unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|];
    destruct (Hpist x ltac:(lia)) as (Hxi & Hxs & _);
    intros [Ho | Hw]; [exact (sat_img_not_owned tfibsegs B LAWS lyc Sc W memc mdc x HAR Hxi Hxs Ho)
                      | unfold coff_win in Hpiwin; unfold TB_ring, TB_sysex, ESTACK in *; lia]
  | ] end.
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_agree tfibsegs 89 Ev (havoc Ev 89 [Z_to_bv 64 (d_dev d); Z_to_bv 64 (d_strips d)]) ssv msv HS
    (env_agree_havoc_ge 89 89 Ev Ev _ ltac:(lia) (env_agree_refl 89 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
  assert (E89 : ew (havoc Ev 89 [Z_to_bv 64 (d_dev d); Z_to_bv 64 (d_strips d)]) 89 = Z_to_bv 64 (d_dev d))
    by exact (ew_havoc_new Ev 89 [Z_to_bv 64 (d_dev d); Z_to_bv 64 (d_strips d)] 0 (Z_to_bv 64 0) ltac:(cbn; lia));
  assert (E90 : ew (havoc Ev 89 [Z_to_bv 64 (d_dev d); Z_to_bv 64 (d_strips d)]) 90 = Z_to_bv 64 (d_strips d))
    by exact (ew_havoc_new Ev 89 [Z_to_bv 64 (d_dev d); Z_to_bv 64 (d_strips d)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
  clear HS. rename HS3 into HS. rgb_rebase HS AG HAE.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 89%nat (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E89, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 90%nat (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E90, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 10%nat) 16 20 16 16
     [YP09.mkChunk 17 (CVal 1 (SOff 90 0)); YP09.mkChunk 16 (CVal 1 (SOff 89 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite (E10 Ev AG), unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val tfibsegs Ev _ p 17 1 (SOff 90 0) (d_strips d));
        [cbn [sv_denot]; rewrite E90, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
        | replace (p + 17) with (p + 16 + Z.of_nat 1) by lia; exact (VP 1%nat ltac:(lia)) ]
      | apply (chunk_ok_val tfibsegs Ev _ p 16 1 (SOff 89 0) (d_dev d));
        [cbn [sv_denot]; rewrite E89, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
        | replace (p + 16) with (p + 16 + Z.of_nat 0) by lia; exact (VP 0%nat ltac:(lia)) ] ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite (E10 Ev AG); evalE AG; rewrite ?unsigned_lit_small by lia;
      unfold YCbq.off_img, YCbqU.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, TFIB_IMG_LO, TFIB_IMG_END in *; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ss HS.
  clear KA VP.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 10%nat (mkAF 1 TFIB_IMG_END 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (E10 Ev AG), unsigned_lit_small by lia; change (2 ^ 3) with 8;
          unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
    rgb_shok [mkSHE 10 16 20]
      ltac:(idtac; lazymatch goal with |- shent_ok _ _ _ _ (mkSHE 10 _ _) =>
        exact (cw_shent_img_off B lyc S2 Wx (ms_mem msx) _ (spZ regs) TB_ring Ev 10 p 16 4 (proj1 HJ) HPimg (E10 Ev AG)
          ltac:(lia) ltac:(lia) (E32' Ev AG)) end) end.
  (* 0x85d24-0x85d4c: beqz s4 (decided, out > 0), the alignment test of p (decided), the check of p + 17 (decided),
     a1 = p->strips, a0 = -11, to bgeu s3,a1 *)
  cw_run ltac:(rgb_awr AG sp sp1 pos).
  rgb_kt AG HJ0 HJ2c HPm.
  lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
  assert (U11 : forall Ev, ew Ev 11 = Z_to_bv 64 (s32 strip mod 2 ^ 64) -> U Ev (SOff 11 0) = s32 strip mod 2 ^ 64)
    by (intros Ev HEv; apply (U_atom Ev 11); [exact HEv | apply rgb_s32_rng; lia]).
  assert (E11m : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 11 = Z_to_bv 64 (s32 strip mod 2 ^ 64))
    by (intros Ev AGv; rewrite (E11 Ev AGv); apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by lia; reflexivity).
  cw_branch Hb1.
  all: rewrite branch_geu_U in Hb1;
       lazymatch type of Hb1 with context [U ?Ev _] =>
         rewrite (U11 Ev (E11m Ev AG)) in Hb1;
         rewrite (U_atom Ev 90 (d_strips d) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E90) ltac:(lia)) in Hb1 end;
       rewrite (rgb_u11_lt strip (d_strips d) ltac:(lia) ltac:(lia)) in Hb1.

  + (* taken: p->strips <= strip, a0 = -11 *)
    apply negb_true_iff, Z.ltb_ge in Hb1.
    rewrite (rgb_spec_strips d strip mask ltac:(lia)).
    rgb_add88 HJ Hfin2 Efa2 AG E10.
    aj_run_to_sh tfibtbl_lib_ok HS HJ 0x85e30; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ.
    rgb_kt AG HJ0 HJ2c HPm.
    rgb_exit_tac HS Hsp1 HJ Hnin HPm HM2 HAR Hotd.
    * exact (rgb_tcj_mono B _ _ _ _ _ _ _ _ (fun _ => False) _ (fun a H => False_ind _ H) KT).
    * cbn [snd cmd_outZ]. eapply rgb_garr8_kept; [rewrite HLbef; exact Hotd | exact KT | exact HGbef].
    * exact HLbef.
  + (* strip < p->strips, so the strip is a byte; 0x85d50-0x85d54 test bit 15 of the mask *)
    apply negb_false_iff, Z.ltb_lt in Hb1.
    assert (E11s : forall Ev, (forall n, (n < 33)%nat -> ew Ev n = ew E n) -> ew Ev 11 = Z_to_bv 64 strip)
      by (intros Ev AGv; rewrite (E11 Ev AGv); f_equal; unfold s32; destruct (Z.ltb_spec strip (2 ^ 31)); lia).
    lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
    rgb_shok (@nil shent) ltac:(fail).
    cw_run ltac:(rgb_awr AG sp sp1 pos).
    rgb_kt AG HJ0 HJ2c HPm.
    lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
    cw_branch Hb2.
    all: lazymatch type of Hb2 with context [sv_denot ?Ev _] =>
           rewrite (rgb_shl48_lt0 Ev mask (E12 Ev AG) ltac:(lia)) in Hb2 end.
    * (* taken: bit 15 set, a0 = -11 *)
      apply Z.ltb_lt in Hb2.
      rewrite (rgb_spec_mask d strip mask ltac:(lia) ltac:(lia)).
      rgb_add88 HJ Hfin2 Efa2 AG E10.
      aj_run_to_sh tfibtbl_lib_ok HS HJ 0x85e30; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ.
      rgb_kt AG HJ0 HJ2c HPm.
      rgb_exit_tac HS Hsp1 HJ Hnin HPm HM2 HAR Hotd.
      -- exact (rgb_tcj_mono B _ _ _ _ _ _ _ _ (fun _ => False) _ (fun a H => False_ind _ H) KT).
      -- cbn [snd cmd_outZ]. eapply rgb_garr8_kept; [rewrite HLbef; exact Hotd | exact KT | exact HGbef].
      -- exact HLbef.
    * (* the mask is 15 bits: the loop, the payload, diginet_sysex_encode *)
      apply Z.ltb_ge in Hb2.
      rewrite (rgb_spec_go d strip mask ltac:(lia) ltac:(lia)), (rgb_u8 _ (rgb_pl0_range mask strip ltac:(lia))).
      set (pl0 := Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)) in *.
      set (b1 := fst (ring_bits mask)) in *. set (b2 := snd (ring_bits mask)) in *.
      assert (HPL0R : 0 <= pl0 < 256) by (apply rgb_pl0_range; lia).
      assert (HB1R : 0 <= b1 < 128)
        by (unfold b1; rewrite <- (rgb_ring_bits_fst E mask (E12 E (fun _ _ => eq_refl)) ltac:(lia)); apply (rgb_acc_range E mask 62 (E12 E (fun _ _ => eq_refl)) ltac:(lia) ltac:(lia))).
      assert (HB2R : 0 <= b2 < 128)
        by (unfold b2; rewrite <- (rgb_ring_bits_snd E mask (E12 E (fun _ _ => eq_refl)) ltac:(lia)); apply (rgb_acc_range E mask 55 (E12 E (fun _ _ => eq_refl)) ltac:(lia) ltac:(lia))).
      (* 0x85d58-0x85db4: the seven iterations, a4 = 3, s5 <<= 63, a0 = p + 16 *)
      lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
      rgb_shok (@nil shent) ltac:(fail).
      cw_run_to ltac:(rgb_awr AG sp sp1 pos) 0x85db8.
      rgb_kt AG HJ0 HJ2c HPm.
      lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
      (* 0x85db8-0x85dd0: the shadow byte of pl := 3 (its first three bytes usable), pl[0..3) := pl0, b1, b2;
         the frame's shadow region back for the store into it, the plain engine (no check in the range) *)
      rgb_add88 HJ Hfin2 Efa2 AG E10.
      aj_run_to_sh tfibtbl_lib_ok HS HJ 0x85dd4; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ.
      rgb_kt AG HJ0 HJ2c HPm.
      lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
      (* pl's shadow byte (region 88), the three payload bytes and the flag address (region 75) *)
      lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
        pose proof (st_ok_region_nth Ev ssv msv 0 _ HS eq_refl) as R88;
        cbn [ms_mem restrict mkst] in R88;
        pose proof (field_of_region Ev _ 88 (shadow_addr F) _ _ _ _ _ 4 1 _ 3 R88 ltac:(rewrite E88; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia)
          ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS4;
        clear R88 end.
      rgb_drop88.
      lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
        rgb_shok [mkSHE 10 16 20]
          ltac:(idtac; lazymatch goal with |- shent_ok _ _ _ _ (mkSHE 10 _ _) =>
            exact (cw_shent_img_off B lyc S2 Wx (ms_mem msx) _ (spZ regs) TB_ring Ev 10 p 16 4 (proj1 HJ) HPimg (E10 Ev AG)
              ltac:(lia) ltac:(lia) (E32' Ev AG)) end) end.
      (* 0x85dd4-0x85df0: the check of p + 16 (decided), a0 = p->device, a1 = 0, a3 = 3, a4 = out (a2 = F + 32 already),
         jal diginet_sysex_encode; the run stores nothing *)
      cw_run_to ltac:(rgb_awr AG sp sp1 pos) 0x85174.
      lazymatch goal with HFr : frame_of _ _ _ _ |- _ => rgb_carry AG HFr VS4 end.
      rgb_kt AG HJ0 HJ2c HPm.
      lazymatch type of HS with st_ok _ ?Ev _ _ => lazymatch type of E75 with ew Ev _ = _ => idtac | _ => rgb_rebase HS AG HAE end end.
      (* the three payload bytes and the flag address, read back from the frame region *)
      lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
        pose proof (st_ok_region_nth Ev ssv msv 1 _ HS eq_refl) as R75;
        cbn [ms_mem restrict mkst] in R75;
        destruct (rgb_byte_of_region Ev _ 75 F _ _ _ _ _ 32 _ pl0 R75 ltac:(rewrite E75; apply unsigned_lit_small; lia)
          ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
          ltac:(lazymatch goal with |- U ?Ev' _ mod 256 = _ =>
                  rewrite (rgb_pl0_val Ev' mask strip (E12 Ev' AG) (E11s Ev' AG) ltac:(lia) ltac:(lia)) end;
                apply Z.mod_small; exact HPL0R)) as (V32 & _);
        destruct (rgb_byte_of_region Ev _ 75 F _ _ _ _ _ 33 _ b1 R75 ltac:(rewrite E75; apply unsigned_lit_small; lia)
          ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
          ltac:(lazymatch goal with |- U ?Ev' _ mod 256 = _ =>
                  change (U Ev' (rgb_acc 62) mod 256 = b1); unfold b1;
                  pose proof (rgb_acc_range Ev' mask 62 (E12 Ev' AG) ltac:(lia) ltac:(lia)) as HR62;
                  rewrite (rgb_ring_bits_fst Ev' mask (E12 Ev' AG) ltac:(lia)) in HR62 |- * end;
                apply Z.mod_small; lia)) as (V33 & _);
        destruct (rgb_byte_of_region Ev _ 75 F _ _ _ _ _ 34 _ b2 R75 ltac:(rewrite E75; apply unsigned_lit_small; lia)
          ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
          ltac:(lazymatch goal with |- U ?Ev' _ mod 256 = _ =>
                  change (U Ev' (rgb_acc 55) mod 256 = b2); unfold b2;
                  pose proof (rgb_acc_range Ev' mask 55 (E12 Ev' AG) ltac:(lia) ltac:(lia)) as HR55;
                  rewrite (rgb_ring_bits_snd Ev' mask (E12 Ev' AG) ltac:(lia)) in HR55 |- * end;
                apply Z.mod_small; lia)) as (V34 & _);
        pose proof (field_of_region Ev _ 75 F _ _ _ _ _ 56 8 _ FL R75 ltac:(rewrite E75; apply unsigned_lit_small; lia)
          ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (_ & _ & _ & (HFL0 & _ & HFLc)); cbn; unfold TB_ring, TB_sysex, ESTACK in *; lia) ltac:(cbn; lia)) as V56b;
        clear R75 end.
      clear V56. rename V56b into V56.
      lazymatch type of V32 with val_mem _ (mrestrict ?Hk ?mk) _ _ _ =>
        pose proof (rgb_pl_garr8 Hk mk F pl0 b1 b2 HPL0R ltac:(lia) ltac:(lia) V32 V33 V34) as VPL end.
      clear V32 V33 V34.
      (* the frame region dropped: the call keeps the stack windows and the personality bytes *)
      lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
        let rs := eval vm_compute in (firstn 1 (ss_mem ssv) ++ skipn 2 (ss_mem ssv)) in
        pose proof (st_ok_submem tfibsegs Ev ssv msv rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
        clear HS; rename HS3 into HS end.
      norm_ss HS.
      (* the call of diginet_sysex_encode through its contract *)
      rename HJ into HJc.
      assert (HFq8 : F / 8 = 8 * (F / 64)) by exact HF8.
      pose proof (rgb_cdst_call B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 pos _ _ sp sp1 out HJ0 HJc Eab Hfrs2 KT
        (proj1 HOUT) ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia) ltac:(lia)) as HOc.
      pose proof (rgb_garr8_kept B TB_ring lyc Sc W memc W _ sp out before ltac:(rewrite HLbef; exact Hotd) KT HGbef) as HGc.
      lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict (w_H ?Wx) ?msv) =>
      rreg HS (1%bv : bv 5) Hq1; rreg HS (2%bv : bv 5) Hq2; rreg HS (3%bv : bv 5) Hq3; rreg HS (4%bv : bv 5) Hq4;
      rreg HS (10%bv : bv 5) Hq10; rreg HS (11%bv : bv 5) Hq11; rreg HS (12%bv : bv 5) Hq12; rreg HS (13%bv : bv 5) Hq13;
      rreg HS (14%bv : bv 5) Hq14;
      assert (Esp4 : spZ (ms_regs msv) = sp1) by (unfold spZ at 1; rewrite Hq2; rewrite ?sv_denot_SOff0; rewrite E70; apply unsigned_lit_small; lia);
      assert (HBS4 : block_shadow (aview tfibsegs (w_H W) (ms_mem msv)) SHADOW_OFF (F + 32) 3);
      [ unfold block_shadow; split; [rewrite HFq; replace (64 * (F / 64) + 32) with ((8 * (F / 64) + 4) * 8) by lia; apply Z_mod_mult|];
        split; [lia|]; intros i Hi; change ((3 + 7) / 8) with 1 in Hi; replace i with 0 by lia;
        assert (Es : shadow_of_addr SHADOW_OFF (F + 32) = shadow_addr F + 4)
          by (unfold shadow_of_addr, shadow_addr; rewrite HFq8; rewrite HFq at 1;
              replace (64 * (F / 64) + 32) with ((8 * (F / 64) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
        rewrite Es, Z.add_0_r; etransitivity; [exact (aview_of_val_mem1 tfibsegs _ _ _ 3 VS4 ltac:(lia)) | reflexivity]
      | ];
      pose proof (sat_frame_rd tfibsegs B LAWS lyc S2 W (ms_mem msv) _ sp1 TB_sysex 0 pos F 32 3 STK sp0 (proj1 HJc) Hfin2
        eq_refl HF64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(change (fs_frame_bytes 0) with 64; lia) HBS4
        ltac:(first [exact Hceil | unfold TB_ring, TB_sysex, ESTACK in *; lia]) ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia)) as Hplrd4;
      eapply (cpw_call Wx Ev ssv msv _ _ _ HS eq_refl);
      [ eapply (SYSEX STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 Wx (ms_mem msv) _ k (ms_regs msv)
                (d_dev d) 0 (F + 32) 3 out [pl0; b1; b2] before);
        [ eapply (cpw_entry B STK sp0 FP ly S W0 mem0 md0 _ lyc Sc lyc S2);
          [ exact HJc
          | rewrite Hq1; apply ret_ok_even; vm_compute; reflexivity
          | unfold raZ; rewrite Hq1, unsigned_lit_small by lia; lia
          | rewrite Hq3; rewrite ?sv_denot_SOff0; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
          | rewrite Hq4; rewrite ?sv_denot_SOff0; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
          | rewrite Esp4; exact Hsp1al16
          | rewrite Esp4; unfold TB_ring, TB_sysex, ESTACK in *; lia
          | rewrite Esp4; lia
          | first [assumption | unfold EV_CDC in *; lia]
          | exact HPm
          | exact Hlive ]
        | split; [lia | rewrite Hq10; rewrite ?sv_denot_SOff0; rewrite E89; reflexivity]
        | split; [lia | rewrite Hq11; reflexivity]
        | rewrite Hq12; cbn [sv_denot]; rewrite E75, unsigned_lit_small by lia; reflexivity
        | rewrite Hq13; reflexivity
        | reflexivity
        | lia
        | rewrite Hq14; rewrite ?sv_denot_SOff0; rewrite (AG 13%nat) by lia; rewrite (EE 13%nat 13%bv eq_refl); exact H13
        | exact Ho4
        | intros _; split; [lia|]; split; [exact VPL|]; rewrite Esp4; split;
          [ exact Hplrd4
          | apply (rgb_fresh_disj2 B lyc Sc out 32 (F + 32) 3 Hotd); [| lia | lia];
            intros a Ha; apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 Wx (ms_mem msv) _ k 0 pos a HJ0 HJc HPm);
            left; unfold frame_rng, in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia ]
        | rewrite Esp4; split; [exact HOc | split; [exact HGc | exact HLbef]] ]
      | ]
      end.
      intros W4 c4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & KT4 & HR4).
      rewrite Esp4 in KT4. change TB_sysex with 4144 in KT4. rewrite Hq1.
      lazymatch goal with |- context [mkst regs4 ?pcv] => change pcv with (Z_to_bv 64 548340) end.
      replace (k + EV_CDC) with k in HJ4 by (unfold EV_CDC; lia).
      (* the kept invariant through the call *)
      pose proof (rgb_tcj_mono B _ _ _ _ _ _ _ _ (fun _ => False) (cenc_wr out) (fun a H => False_ind _ H) KT) as KTo.
      lazymatch type of HJc with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ?mdd _ =>
      pose proof (cw_kept_cj B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ((0, pos) :: own) lyc S2 W mc mdd k W4 mem4
        TB_ring 4144 sp sp1 (cenc_wr out) (cenc_wr out) HJ0 HJc ltac:(rewrite Hfrs2; apply incl_tl, incl_refl) HPm
        ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia) ltac:(lia) ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia) ltac:(lia)
        ltac:(intros a Ha; right; left; split; [exact Ha | intros Hi; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR Hotd Ha Hi)])
        KTo KT4) as KTn;
      (* the frame's flag address after the call: the frame (0, pos) is one of the call's state *)
      assert (KF4 : forall a, (in_zr a (frame_rng lyc (0, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)) ->
        aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W) mc a);
      [ intros a Hza; pose proof KT4 as (_ & _ & _ & K4 & _); apply (K4 0 pos a Hfin2 Hza);
        intros Ho; destruct (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mc mdd k 0 pos a HJ0 HJc HPm
          ltac:(destruct Hza as [Hza | Hza]; [left; exact Hza | right; left; exact Hza])) as (_ & _ & Hb & Hfr);
        destruct (Hotd a Ho) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)];
        [ exact (Hb bb mm (a - bb) Hin ltac:(lia) ltac:(lia)) | exact (proj1 (Hfr cid ps Hin) Hr) ]
      | ] end.
      clear KTo. clear KT. rename KTn into KT.
      lazymatch goal with V : val_mem _ (mrestrict _ ?mc) (F + 56) _ _ |- _ =>
        assert (V56b : val_mem tfibsegs (mrestrict (w_H W4) mem4) (F + 56) 8 FL);
        [ apply (cw_val_mem_kept (w_H W) (w_H W4) mc mem4 _ 8 _); [|exact V56];
          intros x Hx; apply KF4; left; unfold frame_rng, in_zr; cbn [fst snd Z.of_nat Pos.of_succ_nat] in *;
          change (fs_frame_bytes 0) with 64; lia | ] end.
      clear V56 VS4 VPL. rename V56b into V56.
      (* the state at the return address: the spill and the save area kept *)
      pose proof (proj1 HJ4) as HAR4.
      rgb_reseat HS HJ4 HP4 [1; 2]%nat AG HAE
        ltac:(idtac; lazymatch goal with |- region_kept _ ?Ev _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ _) =>
          eapply (region_kept_tcj_stack B Ev 4144 lyc S2 W _ W4 mem4 sp1 (cenc_wr out)); [exact KT4 | evalE AG | |];
          intros a Ha; unfold cenc_wr; pose proof (rgb_tdst_below B LAWS lyc Sc W memc mdc out 32 HAR Hotd ltac:(lia));
          unfold TB_ring, TB_sysex, ESTACK in *; lia end).
      rreg HS (10%bv : bv 5) Hx10. rewrite ?sv_denot_SOff0 in Hx10.
      (* the result of sysex and the frame facts in the call's coordinates *)
      pose proof (Permutation_trans HPerm4 HPm) as HPm4.
      pose proof (proj2 (cw_frame_step MT MTL B lyc Sc lyc S2 ly4 S4 HPm HM2 HPerm4 HMLE4)) as HM4.
      assert (Hfin4 : In (0, pos) (frames S4)) by (rewrite Hfrs4; exact Hfin2).
      assert (Efa4 : forall c q, frame_addr ly4 c q = frame_addr lyc c q).
      { intros c q. unfold frame_addr. destruct (proj1 (proj2 HJ0)) as (_ & _ & _ & _ & _ & EF & _).
        destruct (proj1 (proj2 HJ4)) as (_ & _ & _ & _ & _ & EF4 & _). rewrite EF, EF4. reflexivity. }
      destruct (rgb_sysex_shape (d_dev d) 0 [pl0; b1; b2]) as [(rcv & Hrs & Hrc) | (bs' & dp & Hrs & Hbs')];
        rewrite Hrs in HR4 |- *; destruct HR4 as (HRa0 & HRo); cbn [fst snd] in HRa0, HRo.
      -- (* sysex failed: rc in [-11, -1], the command unchanged; bnez a0 taken, to 0x85e28 *)
         rewrite rgb_with_key_none.
         srr_branch_sh tfibtbl_lib_ok HS.
         all: lazymatch goal with Hb : branch_taken BC_NE _ _ = _ |- _ => rename Hb into Hc1 end.
         2: { exfalso. rewrite branch_ne_U, U_lit in Hc1 by lia.
              lazymatch type of Hc1 with context [U ?Ev ?a0] =>
                assert (Ua : U Ev a0 = rcv + 2 ^ 64)
                  by (unfold U; rreg HS (10%bv : bv 5) Hx; rewrite sv_denot_SOff0, <- Hx, HRa0; unfold w64; rewrite Z_to_bv_unsigned;
                      unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64);
                      rewrite <- (Z_mod_plus_full rcv 1); apply Z.mod_small; lia) end.
              rewrite Ua in Hc1. destruct (Z.eqb_spec (rcv + 2 ^ 64) 0); [lia | discriminate Hc1]. }
         cbn [cmd_outZ] in HRo.
         lazymatch type of Hx10 with _ = ew ?Ev ?j =>
           assert (HA0v : ew Ev j = Z_to_bv 64 rcv) by (rewrite <- Hx10, HRa0; reflexivity) end.
         rgb_add75 HJ4 Hfin4 Efa4 AG V56 E10.
         rgb_add88 HJ4 Hfin4 Efa4 AG E10.
         (* 0x85e28-0x85e2c: the shadow byte of pl back to 0xf8 *)
         pose proof HJ4 as HJ4c.
         aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x85e30; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ4.
         lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2) |- _ =>
           assert (HRo2 : garr8 tfibsegs (mrestrict H m2) out before)
             by (apply (rgb_garr8_run Ev rs H m1 m2 (rgb_wz sp lyc pos) out before HFr);
                 [rgb_wzc AG | rewrite HLbef; exact Hout_nz | lia | rewrite HLbef; lia | exact HRo]) end.
         rgb_kt AG HJ0 HJ4c HPm4.
         rgb_exit_tac HS Hsp1 HJ4 Hnin HPm4 HM4 HAR Hotd.
         ++ exact KT.
         ++ exact HRo2.
         ++ exact HLbef.
      -- (* sysex succeeded: rc = 0; bnez a0 not taken: the alignment test of out, the key store at out + 28 *)
         cbn [with_key].
         srr_branch_sh tfibtbl_lib_ok HS.
         all: lazymatch goal with Hb : branch_taken BC_NE _ _ = _ |- _ => rename Hb into Hc1 end.
         1: { exfalso. rewrite branch_ne_U, U_lit in Hc1 by lia.
              lazymatch type of Hc1 with context [U ?Ev ?a0] =>
                assert (Ua : U Ev a0 = 0)
                  by (unfold U; rreg HS (10%bv : bv 5) Hx; rewrite sv_denot_SOff0, <- Hx, HRa0; reflexivity) end.
              rewrite Ua in Hc1. discriminate Hc1. }
         lazymatch type of Hx10 with _ = ew ?Ev ?j =>
           assert (HA0v : ew Ev j = Z_to_bv 64 0) by (rewrite <- Hx10, HRa0; reflexivity) end.
         pose proof (rgb_tdst_mono B lyc Sc ly4 S4 out 32 Hotd
           ltac:(intros bb mm Hin; exact (Permutation_in _ (Permutation_sym HPm4) Hin))
           ltac:(intros c q Hin; rewrite Hfrs4, Hfrs2; right; exact Hin) Efa4) as Hotd4.
         pose proof asan_consts as (CC1 & _).
         pose proof (rgb_tdst_below B LAWS lyc Sc W memc mdc out 32 HAR Hotd ltac:(lia)) as Hob.
         (* the command's last word as a writable region on atom 13, with a fact on out (4-aligned) that keeps its
            shadow in the band *)
         lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
         pose proof (st_ok_add_fact tfibsegs Ev ssx msx 13%nat (mkAF 4096 (0x7fffff800000 - 32) 2) HS
           ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (E13 Ev AG), unsigned_lit_small by lia;
                 change (2 ^ 2) with 4; lia)) as HS3;
         clear HS; rename HS3 into HS end.
         lazymatch type of HS with st_ok _ ?Ev _ _ =>
         pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 13%nat) 28 32 28 32 []) HS eq_refl
           ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
                 rewrite (E13 Ev AG), unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
                 intros o Ho; apply (apresent_writable tfibsegs); exact (rgb_tdst_present B LAWS ly4 S4 W4 mem4 md4 out 32 (out + o) HAR4 Hotd4 ltac:(lia)))
           ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
             cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
             rewrite (E13 Ev AG); evalE AG; rewrite ?unsigned_lit_small by lia;
             unfold cpers_disj in HPD; unfold TB_ring, TB_sysex, ESTACK in *; repeat split; lia)) as HS3;
         clear HS; rename HS3 into HS end.
         norm_ss HS.
         try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end.
         lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
         assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32] Ev (mrestrict (w_H Wx) (ms_mem msx)));
         [ apply Forall_cons; [|apply Forall_nil];
           apply (cw_shent_ra Wx (ms_mem msx) Ev 13 out 32);
           [ apply (rgb_ra_tdst B LAWS lyc Sc W memc mdc ly4 S4 Wx (ms_mem msx) md4 out 32 HAR HAR4 Hotd);
             [ intros bb mm Hin; exact (Permutation_in _ (Permutation_sym HPm4) Hin)
             | intros cid ps a Hin Hr; pose proof KT as (_ & _ & _ & K4 & _); apply (K4 cid ps a Hin (or_intror Hr));
               unfold cenc_wr; intros Ha;
               destruct (al_frames _ _ LAWS _ _ _ _ _ cid ps HAR Hin) as (_ & _ & _ & _);
               destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid ps HAR Hin) as (Hc4096 & Hcceil & _);
               unfold in_zr in Hr; cbn [fst snd] in Hr;
               pose proof (fs_frame_bytes_nonneg cid);
               pose proof (shadow_addr_bounds (frame_addr lyc cid ps) ltac:(unfold kHighMemEnd in *; lia)) as Hsb;
               assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia);
               pose proof (Z.div_mod (frame_addr lyc cid ps) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (frame_addr lyc cid ps) 8 ltac:(lia));
               pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia));
               pose proof (Z.div_le_mono (frame_addr lyc cid ps + fs_frame_bytes cid) 0x7fffff800000 8 ltac:(lia) ltac:(lia));
               pose proof (Z.div_mod (frame_addr lyc cid ps + fs_frame_bytes cid) 8 ltac:(lia));
               pose proof (Z.mod_pos_bound (frame_addr lyc cid ps + fs_frame_bytes cid) 8 ltac:(lia));
               change (0x7fffff800000 / 8) with 0xffffff00000 in *;
               unfold amem_range, shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *; lia
             | exact Hora ]
           | exact Hoam | lia | lia | lia | exact (E13 Ev AG) | exact (E32' Ev AG) ]
         | ] end.
         (* 0x85df8-0x85e24: the alignment test of out (decided), s4 = out + 28, the check of its shadow (decided),
            sw (strip | 0x30000) at out + 28 *)
         cw_run_to ltac:(rgb_awr13 AG sp sp1 pos E13 Hotw HPm4 Efa4) 0x85e28.
         (* the key and the kept invariant through the store *)
         lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
           pose proof (cw_kept_step B LAWS TB_ring lyc Sc W memc mdc W4 m1 m2 sp (cenc_wr out) (in_wrange Ev rs)
             ltac:(unfold TB_ring, TB_sysex, ESTACK in *; lia) HAR KT ltac:(rgb_frx HFr)
             ltac:(idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
                   intros a (r & Hr & Hb);
                   lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
                   repeat (destruct Hr as [<- | Hr];
                     [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia; rewrite ?(E13 _ AG) in Hb; revert Hb; evalE AG; intros Hb;
                       rewrite ?unsigned_lit_small in Hb by lia;
                       first [ left; unfold TB_ring, TB_sysex, ESTACK in *; lia
                             | right; left; split; [unfold cenc_wr; lia|];
                               intros Hi; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR Hotd ltac:(lia) Hi) ]
                     | ]); destruct Hr)
             ltac:(idtac; let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp])) as KT1;
           assert (HZ13 : forall a, in_wrange Ev rs a -> (sp - TB_ring <= a < sp) \/ (out + 28 <= a < out + 32));
           [ let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
             intros a (r & Hr & Hb);
             lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
             repeat (destruct Hr as [<- | Hr];
               [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia; rewrite ?(E13 _ AG) in Hb; revert Hb; evalE AG; intros Hb;
                 rewrite ?unsigned_lit_small in Hb by lia; first [left; unfold TB_ring, TB_sysex, ESTACK in *; lia | right; lia]
               | ]); destruct Hr
           | ];
           assert (V56c : val_mem tfibsegs (mrestrict H m2) (F + 56) 8 FL);
           [ apply (cw_val_mem_kept H H m1 m2 _ 8 _); [|exact V56];
             let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
             unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 x)); [reflexivity|];
             rewrite unsigned_lit_small by lia;
             let Hw := fresh "Hw" in intros Hw; destruct (HZ13 x Hw) as [Hw1 | Hw1];
             [ unfold TB_ring, TB_sysex, ESTACK in *; lia
             | apply (Hout_nz x ltac:(lia)); right; left; unfold frame_rng, in_zr; cbn [fst snd];
               change (fs_frame_bytes 0) with 64; lia ]
           | ];
           assert (HRo28 : garr8 tfibsegs (mrestrict H m2) out (firstn 28 (cmd_outZ before (Some (bs', 0, dp)))));
           [ apply (rgb_garr8_run Ev rs H m1 m2 (fun a => (sp - TB_ring <= a < sp) \/ (out + 28 <= a < out + 32)) out _ HFr);
             [ exact HZ13
             | rewrite firstn_length, (rgb_cmd_len before bs' 0 dp HLbef Hbs'); intros a Ha;
               unfold TB_ring, TB_sysex, ESTACK in *; cbn [Nat.min Z.of_nat] in Ha; lia
             | lia | rewrite firstn_length, (rgb_cmd_len before bs' 0 dp HLbef Hbs'); cbn; lia
             | apply rgb_garr8_firstn; exact HRo ]
           | ];
           clear KT; rename KT1 into KT end.
         clear_frames. rgb_rebase HS AG HAE.
         assert (HKEY : 0 <= KEY 3 strip < 2 ^ 32)
           by (unfold KEY; change 0xffff with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; apply (Z_lor_bound _ _ 32); lia).
         lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
           pose proof (st_ok_region_nth Ev ssv msv 0 _ HS eq_refl) as R13;
           cbn [ms_mem restrict mkst] in R13;
           pose proof (field_of_region Ev _ 13 out _ _ _ _ _ 28 4 _ (KEY 3 strip) R13 ltac:(rewrite (E13 Ev AG); apply unsigned_lit_small; lia)
             ltac:(cbn; tauto)
             ltac:(rewrite denot_lit_U; f_equal; apply (rgb_key_val Ev strip (E11s Ev AG)); lia)
             ltac:(cbn; lia) ltac:(cbn; lia)) as V28;
           clear R13 end.
         lazymatch type of HRo28 with garr8 _ (mrestrict ?Hk ?mk) _ _ =>
         assert (HRk : garr8 tfibsegs (mrestrict Hk mk) out (cmd_outZ before (Some (bs', KEY 3 strip, dp))));
         [ rewrite (rgb_cmd_key before bs' dp 0 (KEY 3 strip) HLbef Hbs');
           apply rgb_garr8_app; [exact HRo28|];
           rewrite firstn_length, (rgb_cmd_len before bs' 0 dp HLbef Hbs'); cbn [Nat.min Z.of_nat Pos.of_succ_nat];
           apply rgb_le4_garr8; [exact HKEY | exact V28]
         | ] end.
         clear HRo28 V28 HRo V56. rename V56c into V56.
         (* the command's region dropped; the frame and its shadow back *)
         lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
           let rs := eval vm_compute in (tl (ss_mem ssv)) in
           pose proof (st_ok_submem tfibsegs Ev ssv msv rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
           clear HS; rename HS3 into HS end.
         norm_ss HS.
         rgb_add75 HJ4 Hfin4 Efa4 AG V56 E10.
         rgb_add88 HJ4 Hfin4 Efa4 AG E10.
         (* 0x85e28-0x85e2c: the shadow byte of pl back to 0xf8 *)
         pose proof HJ4 as HJ4c.
         aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x85e30; [cw_awrA; rgb_awr AG sp sp1 pos |]. cw_ajA HJ4.
         lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2) |- _ =>
           assert (HRk2 : garr8 tfibsegs (mrestrict H m2) out (cmd_outZ before (Some (bs', KEY 3 strip, dp))))
             by (apply (rgb_garr8_run Ev rs H m1 m2 (rgb_wz sp lyc pos) out _ HFr);
                 [ rgb_wzc AG | rewrite (rgb_cmd_len before bs' (KEY 3 strip) dp HLbef Hbs'); exact Hout_nz | lia
                 | rewrite (rgb_cmd_len before bs' (KEY 3 strip) dp HLbef Hbs'); lia | exact HRk ]) end.
         rgb_kt AG HJ0 HJ4c HPm4.
         rgb_exit_tac HS Hsp1 HJ4 Hnin HPm4 HM4 HAR Hotd.
         ++ exact KT.
         ++ exact HRk2.
         ++ exact (rgb_cmd_len before bs' (KEY 3 strip) dp HLbef Hbs').
Qed.
End e.

(* diginet_ring_encode (image B 0x85c1c) meets its B contract, given the class-0 side-stack frame request and
   diginet_sysex_encode's own B contract. *)
Theorem diginet_ring_encode_B_holds : astack_malloc_realizes tfibsegs B 0 ->
cdcU_sysex_specX tfibsegs B MT 0x85174 -> cdcU_ring_specX tfibsegs B MT 0x85c1c.
Proof.
intros ASM0 SYSEX. unfold cdcU_ring_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip mask out before
  HE H10 HPA Hp8 H11 H12 H13 Ho4 HOUT HOOB HPD HFR.
exact (rgb_walk ASM0 SYSEX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip mask out before
  HE H10 HPA Hp8 H11 H12 H13 Ho4 HOUT HOOB HPD HFR).
Qed.
End d.
End b.
