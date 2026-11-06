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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 513 of its 553 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s12 of the test
   harness's entry function LLVMFuzzerTestOneInput (0x84d34), segments S01 and S02 of the harness's structure map section 2.3:
   - lt_seg_S01: K84eb8 -> K84f84, 0x84eb8 .. 0x84f80: 24(s1) := FR, the three header bytes cap / flags / nfiles
     with their instrumented checks 1-3 (the checks' slow blocks 0x85dd0, 0x85e04, 0x85e10), the mulhu by the cell
     mod40A (no check on that load), 16(s1) / 40(s1), s3 := FR, the cursor s4 / s8, s9 := nfiles, malloc(16616);
   - lt_seg_S02: K84f84 -> K84f98, 0x84f84 .. 0x84f94: s6 := c, s2 := 0x2000, calloc(1, 9236).
   Each proves its statement of LLVMFuzzerTestOneInput_defs.v exactly (lt_seg_S01_stmt, lt_seg_S02_stmt).

   THE FORM: plugin-hostd/fuzz_command's harness walk (origin/ossv/recipes 501c0d516c69): a seed symbolic state at
   the cut (every register its own atom, the read regions, the frame-slot write window, the facts that decide the
   branches), one paj_run_tok per straight stretch (its _s23.v:394-401 for the header bytes, whose checks vanish by
   the payload block's shadow entry), the allocator call by the kit's call step (_s41.v:470-544 aw_malloc_loc, here
   LLVMFuzzerTestOneInput_s12k.v's lt_malloc_at / lt_calloc_at), and the next cut's premises from the run's
   registers (prreg) and the call's post.
   The code: dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s lines 99-155 (listing SegList.v slots 97-152). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02
  LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s12k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Variable cstk : Z.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (pa_sigma SS___interceptor_trampoline_calloc) cstk.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- segment S02: 0x84f84 .. 0x84f94, then calloc(1, 9236) to K84f98 ---- *)
Theorem lt_seg_S02 : lt_seg_S02_stmt B MT.
Proof.
unfold lt_seg_S02_stmt, LT_K84f84_stmt.
intros HKA cx ly S W regs mem md k acc c HB Hfrm HC HH R10 R19 R20 R21 R24 R25 HSL.
pose proof (HKA fx) as HK. clear HKA.
assert (Hnf : 1 <= x_nf cx <= 4) by exact (lt_nfiles_range (x_pl cx)).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s12_seed0 LO_K84f84 W regs mem) as HS.
assert (SHOK : sh_ok SEGS S12x [] (s12_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s12_E regs [])) by (unfold s12_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s12_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s12_E_reg regs [] n rr Hn)).
pose proof HC as (HF & _). pose proof (proj1 HF) as HJ.
remember (s12_E regs []) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x84f84 .. 0x84f94: s6 := a0 (c), s2 := 0x2000, a1 := 0x2414, a0 := 1, jal calloc *)
paj_run_tok RUN HS HJ SHOK S12span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (22%bv : bv 5) P22.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 24; 25]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s12_nowin_kept E W mem (ms_mem ms) HFr) as KM.
pose proof (lk_core_run B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regs mem md k acc
  (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
eapply (lt_calloc_at B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W (ms_regs ms) (ms_mem ms) md1
  k acc (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] 1 9236 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [lk_bsum snd]. unfold seg_spec.SEG_C_SIZE, LIVE_LTOI. lia.
- rewrite P10. reflexivity.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 m HC2 HHm HZ HPr Hres HKS.
  replace (1 * 9236) with seg_spec.SEG_M_SIZE in HC2, HHm, HZ by reflexivity.
  replace (7 + 2 * x_nf cx - 1) with (6 + 2 * x_nf cx) in HC2 by ring.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (lk_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT seg_spec.SEG_M_SIZE) c m HB Hfrm HC2).
  + apply (lk_hblk B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right. left. reflexivity.
  + exact HHm.
  + exact HZ.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P18. reflexivity.
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite (Hpres 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 20%bv ltac:(cbn; tauto)). exact R20.
  + rewrite (Hpres 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite (Hpres 22%bv 22) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P22, (EEo 10%nat 10%bv eq_refl). exact R10.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 24%bv ltac:(cbn; tauto)). exact R24.
  + rewrite (Hpres 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 25%bv ltac:(cbn; tauto)). exact R25.
  + pose proof (lk_sp B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx HB)
      as (_ & Hsp0 & Hsp47 & _ & Hs1lo & Hs1hi).
    intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 16 <= o <= 40) by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
    apply (lk_word_kept (rdW W mem)); [|exact HSL]. intros x Hx.
    pose proof asan_consts as (C1 & _). unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
    rewrite (HKS x) by lia. apply KM. lia.
Qed.

(* ---- segment S01 ---- *)
(* the payload's bytes at a point of the walk: the entry's (garr8), kept by the journal (a block byte is not in the
   footprint longl, an image object) *)
Lemma s1_pay : forall cx ly S (W : world SEGS) regs mem md k acc rem o O,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O -> 0 < x_n cx ->
  forall j, (j < length (x_pl cx))%nat -> rdW W mem (x_p cx + Z.of_nat j) = Some (nth j (seg_spec.seg_in (x_pl cx)) 0).
Proof.
intros cx ly S W regs mem md k acc rem o O HB HC Hn j Hj.
pose proof HB as (_ & _ & _ & HIMG & _ & _ & Hpay & Hlen & Hgarr & _).
destruct Hpay as [[Hn0 _] | [_ Hin0]]; [lia|].
destruct HC as (HF & _ & HBL & _). pose proof (proj1 HF) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
{ unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0. }
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
pose proof (s1_byte_rng (x_pl cx) j) as Hrng.
rewrite (F2 (x_p cx) (x_n cx) (Z.of_nat j) Hin0 Hin ltac:(lia)).
- unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j Hgarr ltac:(rewrite length_map; exact Hj)). cbn [option_map].
  f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hrng.
- intros (r & Hr & Hra). unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra.
  destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hli & _).
  destruct (Hli (x_p cx + Z.of_nat j) ltac:(unfold LONGL_N in *; lia)) as (Himg & _).
  assert (Hblk : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= x_p cx + Z.of_nat j < p0 + req_size n0)
    by (exists (x_p cx), (x_n cx); split; [exact Hin | lia]).
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md (x_p cx + Z.of_nat j) HAR (or_introl Hblk)) Himg).
Qed.
(* the shadow entry of the h header bytes: they lie in the payload's live block *)
Lemma s1_shok : forall ly S (W : world SEGS) mem md E p n h,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  ew E 5 = Z_to_bv 64 SHADOW_OFF -> ew E 24 = Z_to_bv 64 p -> 0 < h -> h <= n ->
  sh_ok SEGS S12x (s1_SH h) E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E p n h HAR Hin E5 E24 Hh Hhn.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hceil & Happ & _ & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
unfold sh_ok, s1_SH. replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E S12x 24 p h p 0 h).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
- unfold S12x. rewrite (U_atom E 5 SHADOW_OFF E5) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite (U_atom E 24 p E24) by lia. reflexivity.
- lia.
- lia.
- intros x Hx Hs. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF in Hs.
  destruct Happ as [_ [Ha | [Ha1 Ha2]]]; lia.
Qed.
(* the call of malloc(16616) at 0x84f80 after S01's run, to K84f84 (the run's facts in abstract form) *)
Lemma s1_finish : forall cx ly S (W : world SEGS) regs mem md acc regs' mem' md',
  LT_K84f84_stmt B MT ->
  lt_base B MT cx -> sa_frm0 ->
  lt_core B MT cx ly S W regs mem md 0 acc (EV_LTOI (x_pl cx)) LFO0 [] ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 16 <= a < x_s1 cx + 48) -> rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 10 = w64 seg_spec.SEG_C_SIZE -> getr regs' 1 = Z_to_bv 64 (BASE + LO_K84f84) ->
  getr regs' 19 = w64 (x_fr cx) -> getr regs' 20 = w64 (x_curn cx 0) -> getr regs' 21 = w64 (x_sh cx) ->
  getr regs' 24 = w64 (x_cur cx 0) -> getr regs' 25 = w64 (x_nf cx) ->
  lt_slots cx (rdW W mem') [(16, x_flags cx); (24, x_fr cx); (40, x_cap cx)] ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_malloc)) mem' (seg_rom SEGS)) md')
    (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md acc regs' mem' md' HK HB Hfrm HC HJ' HKM P2 P3 P4 P8 P9 P10 P1 P19 P20 P21 P24 P25 HSL.
assert (Hnf : 1 <= x_nf cx <= 4) by exact (lt_nfiles_range (x_pl cx)).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (lk_core_run B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regs mem md 0 acc (EV_LTOI (x_pl cx))
  LFO0 [] regs' mem' md' 16 48 HB HC HJ' HKM ltac:(lia) ltac:(lia) P2 P3 P4 P8 P9) as HC1.
apply (lt_malloc_at B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regs' mem' md' 0 acc (EV_LTOI (x_pl cx))
  LFO0 [] seg_spec.SEG_C_SIZE (Z_to_bv 64 (BASE + LO_K84f84)) _ HB HC1).
- unfold EV_LTOI, x_nf in *. lia.
- unfold seg_spec.SEG_C_SIZE. lia.
- cbn [lk_bsum]. unfold seg_spec.SEG_C_SIZE, LIVE_LTOI. lia.
- exact P10.
- exact P1.
- apply ret_ok_codeptr_v; [unfold LO_K84f84; lia | reflexivity].
- unfold LO_K84f84. rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 c HC2 HH HPr Hres HKS.
  replace (EV_LTOI (x_pl cx) - 1) with (7 + 2 * x_nf cx) in HC2 by (unfold EV_LTOI, x_nf; lia).
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs' r)
    by (intros r z Hz Hr; exact (lk_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (0 + 1) (acc + mo_malloc MT seg_spec.SEG_C_SIZE) c HB Hfrm HC2 HH Hres).
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact P19.
  + rewrite (Hpres 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact P20.
  + rewrite (Hpres 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact P21.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact P24.
  + rewrite (Hpres 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact P25.
  + pose proof (lk_sp B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx HB)
      as (_ & Hsp0 & Hsp47 & _ & Hs1lo & Hs1hi).
    intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 16 <= o <= 40) by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
    apply (lk_word_kept (rdW W mem')); [|exact HSL]. intros x Hx.
    unfold LTOI_FRAME_MAX in Hs1lo. apply HKS. lia.
Qed.

(* a register of a state stuck at a call, as the symbolic state names it (prreg without the normalisation) *)
Ltac s1_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac s1_atom := repeat (rewrite ew_ewset_other by lia); assumption.
Lemma s1_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Theorem lt_seg_S01 : lt_seg_S01_stmt B MT.
Proof.
unfold lt_seg_S01_stmt, LT_K84eb8_stmt.
intros HKA cx ly S W regs mem md acc HB Hfrm HC R5 R16 R17 R20 R21 R24.
pose proof (HKA fx) as HK. clear HKA.
pose proof (lk_sp B MT MTL TL IMGS BSYM AMALLOC4 cstk HCSTK ACALLOC4 cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR, Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpay & Hlen & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR ltac:(rewrite Hfrs; left; reflexivity))
  as (Hfrb0 & Hfrb1 & _).
rewrite (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ LT_FCLS (x_fpos cx)) in Hfrb0, Hfrb1.
fold (x_fr cx) in Hfrb0, Hfrb1. change (fs_frame_bytes LT_FCLS) with 512 in Hfrb1.
pose proof (s1_model (x_pl cx)) as (Mcap & Mfl & Mnf & Mcn & Mca).
pose proof (s1_byte_rng (x_pl cx) 0) as B0. pose proof (s1_byte_rng (x_pl cx) 1) as B1.
pose proof (s1_byte_rng (x_pl cx) 2) as B2.
set (b0 := nth 0 (seg_spec.seg_in (x_pl cx)) 0) in *. set (b1 := nth 1 (seg_spec.seg_in (x_pl cx)) 0) in *.
set (b2 := nth 2 (seg_spec.seg_in (x_pl cx)) 0) in *.
assert (HV4 : VAL (A_OBJ 4) = mod40A).
{ rewrite (VOBJS 4%nat); [vm_compute; reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity]. }
pose proof HI as (_ & (Hm40 & Hm40i & _) & _).
assert (HSLW : forall a, x_s1 cx + 16 <= a < x_s1 cx + 48 -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; unfold STK_LLVMFuzzerTestOneInput; lia).
assert (Hd3 : mod40A + 8 <= x_s1 cx + 16) by (unfold mod40A; lia).
assert (Hs1r : 0x7fff7f800000 <= x_s1 cx <= 2 ^ 47) by lia.
assert (U20 : bv_unsigned (getr regs 20) = x_n cx).
{ rewrite R20. unfold w64. apply YP03.unsigned_lit_small. lia. }
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s12_E regs (s1_extra b0 b1 b2)) n = getr regs rr)
  by (intros n rr Hn; exact (s12_E_reg regs _ n rr Hn)).
assert (E32 : ew (s12_E regs (s1_extra b0 b1 b2)) 32 = Z_to_bv 64 b0)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (s12_E regs (s1_extra b0 b1 b2)) 33 = Z_to_bv 64 b1)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (s12_E regs (s1_extra b0 b1 b2)) 34 = Z_to_bv 64 b2)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HEI : img_env VAL A_LIM (s12_E regs (s1_extra b0 b1 b2))) by (unfold s12_E; apply Eimg_env).
assert (Hncase : x_n cx = 0 \/ x_n cx = 1 \/ x_n cx = 2 \/ 3 <= x_n cx) by lia.
destruct Hncase as [Hn0 | [Hn1 | [Hn2 | Hn3]]].
4: {
(* ---- n >= 3: three header bytes ---- *)
destruct Hpay as [[Hz _] | [Hrng Hin0]]; [lia|].
assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
{ unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0. }
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
assert (Rd0 : rdW W mem (x_p cx) = Some b0).
{ rewrite <- (Z.add_0_r (x_p cx)). apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 0%nat). lia. }
assert (Rd1 : rdW W mem (x_p cx + 1) = Some b1)
  by (apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 1%nat); lia).
assert (Rd2 : rdW W mem (x_p cx + 2) = Some b2)
  by (apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 2%nat); lia).
assert (Hd2 : x_p cx + 3 <= mod40A \/ mod40A + 8 <= x_p cx).
{ destruct (Z_le_gt_dec (x_p cx + 3) mod40A) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (mod40A + 8) (x_p cx)) as [H'|H']; [right; exact H'|]. exfalso.
  destruct (Hm40i (Z.max (x_p cx) mod40A) ltac:(lia)) as (Himg & _).
  assert (Hblk : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= Z.max (x_p cx) mod40A < p0 + req_size n0)
    by (exists (x_p cx), (x_n cx); split; [exact Hin | lia]).
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md (Z.max (x_p cx) mod40A) HAR (or_introl Hblk)) Himg). }
pose proof (s1_seed 3 3 (2 ^ 26 - 1) W regs mem b0 b1 b2 (x_p cx) (x_s1 cx) ltac:(lia) R5 R9 R24 Hs1r Hs1al
  ltac:(lia) ltac:(lia) B0 B1 B2 (fun _ => Rd0) (fun _ => Rd1) (fun _ => Rd2) HSLW Hm40 HV4 ltac:(lia) Hd2 Hd3) as HS.
pose proof (s1_shok ly S W mem md (s12_E regs (s1_extra b0 b1 b2)) (x_p cx) (x_n cx) 3 HAR Hin
  ltac:(rewrite (EE 5%nat 5%bv eq_refl); exact R5) ltac:(rewrite (EE 24%nat 24%bv eq_refl); exact R24)
  ltac:(lia) ltac:(lia)) as SHOK.
remember (s12_E regs (s1_extra b0 b1 b2)) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x84eb8 .. 0x84f80: 24(s1) := FR; n <> 0; check 1, byte 0, mod40A, cap into 40(s1), s9 := 1; n <> 1; check 2,
   byte 1 into 16(s1); n <> 2; check 3, s3 := FR, byte 2, s4 := n - 3, s8 := p + 3, s9 := (b2 & 3) + 1;
   a0 := 16616, jal malloc *)
paj_run_tok RUN HS HJ SHOK S12span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0' ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0' bc fr ly0 own) end.
  eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold STK_LLVMFuzzerTestOneInput. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
assert (U9' : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia).
pose proof (s1_kept E W mem (ms_mem ms) 3 (x_s1 cx) HFr U9') as KM.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
pose proof (s1_slot _ _ _ _ _ 16 _ HM ltac:(left; reflexivity) ltac:(left; reflexivity)) as SL16.
pose proof (s1_slot _ _ _ _ _ 40 _ HM ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as SL40.
pose proof (s1_slot _ _ _ _ _ 24 _ HM ltac:(left; reflexivity) ltac:(right; right; left; reflexivity)) as SL24.
cbn [YP09.r_base base_val] in SL16, SL40, SL24.
repeat (rewrite ew_ewset_other in SL16, SL40, SL24 by lia).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20. prreg HS (24%bv : bv 5) P24.
s1_prraw HS (25%bv : bv 5) P25.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 21]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EE; reflexivity | ]).
  destruct Hr. }
apply (s1_finish cx ly S W regs mem md acc (ms_regs ms) (ms_mem ms) md1 HK HB Hfrm HC HJ KM
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))).
- rewrite P10. reflexivity.
- exact P1.
- rewrite P19, (EE 17%nat 17%bv eq_refl). exact R17.
- rewrite P20, (EE 20%nat 20%bv eq_refl), R20. unfold w64. rewrite YP03.unsigned_lit_small by lia.
  f_equal. unfold x_curn. rewrite Mcn. lia.
- rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
- rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. rewrite YP03.unsigned_lit_small by lia.
  f_equal. unfold x_cur. rewrite Mca. lia.
- apply (s1_reg_U _ _ _ _ _ P25). unfold x_nf. rewrite Mnf. apply s1_U_nf; [s1_atom | exact B2].
- rewrite (EE 9%nat 9%bv eq_refl), R9 in SL16, SL40, SL24.
  unfold w64 in SL16, SL40, SL24. rewrite YP03.unsigned_lit_small in SL16, SL40, SL24 by lia.
  intros o v Hio. cbn [In] in Hio. destruct Hio as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <-.
  + rewrite SL16. f_equal. unfold x_flags. rewrite Mfl. apply s1_U_ext8; [s1_atom | exact B1].
  + rewrite SL24. f_equal. apply U_atom; [|unfold x_fr in *; lia].
    repeat (rewrite ew_ewset_other by lia). rewrite (EE 16%nat 16%bv eq_refl). exact R16.
  + rewrite SL40. f_equal. unfold x_cap. rewrite Mcap. apply s1_U_cap; [s1_atom | exact B0].
}
- (* ---- n = 0: no header byte (the empty object); s4 pinned to 0 ---- *)
  destruct Hpay as [[_ Hpe] | [Hrng _]]; [|lia].
  assert (Hb0z : b0 = 0) by (unfold b0, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  assert (Hb1z : b1 = 0) by (unfold b1, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  assert (Hb2z : b2 = 0) by (unfold b2, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  pose proof (s1_seed 0 0 0 W regs mem b0 b1 b2 (x_p cx) (x_s1 cx) ltac:(lia) R5 R9 R24 Hs1r Hs1al
    ltac:(rewrite Hpe; unfold emptyA; lia) ltac:(lia) B0 B1 B2 ltac:(intros Hc; exfalso; lia)
    ltac:(intros Hc; exfalso; lia) ltac:(intros Hc; exfalso; lia) HSLW Hm40 HV4
    ltac:(rewrite Hpe; unfold emptyA; lia) ltac:(right; rewrite Hpe; unfold emptyA, mod40A; lia) Hd3) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ 20%bv 0 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite R20, Hn0; reflexivity)
    eq_refl) as HS. clear HS0.
  assert (SHOK : sh_ok SEGS S12x (s1_SH 0) (s12_E regs (s1_extra b0 b1 b2)) (mrestrict (w_H W) mem)) by apply Forall_nil.
  remember (s12_E regs (s1_extra b0 b1 b2)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* 0x84eb8 .. 0x84f80: 24(s1) := FR; n = 0: s3 := FR, 16(s1) := 0, 40(s1) := 0, s9 := 1; a0 := 16616,
     jal malloc *)
  paj_run_tok RUN HS HJ SHOK S12span.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0' ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0' bc fr ly0 own) end.
    eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia | |].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold STK_LLVMFuzzerTestOneInput. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  assert (U9' : bv_unsigned (ew E 9) = x_s1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia).
  pose proof (s1_kept E W mem (ms_mem ms) 0 (x_s1 cx) HFr U9') as KM.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (s1_slot _ _ _ _ _ 40 _ HM ltac:(left; reflexivity) ltac:(left; reflexivity)) as SL40.
  pose proof (s1_slot _ _ _ _ _ 16 _ HM ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as SL16.
  pose proof (s1_slot _ _ _ _ _ 24 _ HM ltac:(left; reflexivity) ltac:(right; right; left; reflexivity)) as SL24.
  cbn [YP09.r_base base_val] in SL16, SL40, SL24.
  repeat (rewrite ew_ewset_other in SL16, SL40, SL24 by lia).
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 21]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
        rewrite P; apply EE; reflexivity | ]).
    destruct Hr. }
  apply (s1_finish cx ly S W regs mem md acc (ms_regs ms) (ms_mem ms) md1 HK HB Hfrm HC HJ KM
    (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
    (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))).
  + rewrite P10. reflexivity.
  + exact P1.
  + rewrite P19, (EE 17%nat 17%bv eq_refl). exact R17.
  + rewrite P20. unfold w64. f_equal. unfold x_curn. rewrite Mcn. lia.
  + rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. f_equal. unfold x_cur. rewrite Mca. lia.
  + rewrite P25. unfold w64. f_equal. unfold x_nf. rewrite Mnf, Hb2z. reflexivity.
  + rewrite (EE 9%nat 9%bv eq_refl), R9 in SL16, SL40, SL24.
    unfold w64 in SL16, SL40, SL24. rewrite YP03.unsigned_lit_small in SL16, SL40, SL24 by lia.
    intros o v Hio. cbn [In] in Hio. destruct Hio as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <-.
    * rewrite SL16. f_equal. rewrite U_lit by lia. unfold x_flags. rewrite Mfl, Hb1z. reflexivity.
    * rewrite SL24. f_equal. apply U_atom; [|unfold x_fr in *; lia].
      repeat (rewrite ew_ewset_other by lia). rewrite (EE 16%nat 16%bv eq_refl). exact R16.
    * rewrite SL40. f_equal. rewrite U_lit by lia. unfold x_cap. rewrite Mcap, Hb0z. reflexivity.
- (* ---- n = 1: one header byte; s4 pinned to 1 ---- *)
  destruct Hpay as [[Hz _] | [Hrng Hin0]]; [lia|].
  assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
  { unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0. }
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
  pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
  assert (Rd0 : rdW W mem (x_p cx) = Some b0).
  { rewrite <- (Z.add_0_r (x_p cx)). apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 0%nat). lia. }
  assert (Hb1z : b1 = 0) by (unfold b1, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  assert (Hb2z : b2 = 0) by (unfold b2, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  assert (Hd2 : x_p cx + 1 <= mod40A \/ mod40A + 8 <= x_p cx).
  { destruct (Z_le_gt_dec (x_p cx + 1) mod40A) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (mod40A + 8) (x_p cx)) as [H'|H']; [right; exact H'|]. exfalso.
    destruct (Hm40i (Z.max (x_p cx) mod40A) ltac:(lia)) as (Himg & _).
    assert (Hblk : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= Z.max (x_p cx) mod40A < p0 + req_size n0)
      by (exists (x_p cx), (x_n cx); split; [exact Hin | lia]).
    exact (proj2 (al_client_img _ _ LAWS ly S W mem md (Z.max (x_p cx) mod40A) HAR (or_introl Hblk)) Himg). }
  pose proof (s1_seed 1 1 1 W regs mem b0 b1 b2 (x_p cx) (x_s1 cx) ltac:(lia) R5 R9 R24 Hs1r Hs1al
    ltac:(lia) ltac:(lia) B0 B1 B2 (fun _ => Rd0) ltac:(intros Hc; exfalso; lia) ltac:(intros Hc; exfalso; lia)
    HSLW Hm40 HV4 ltac:(lia) Hd2 Hd3) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ 20%bv 1 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite R20, Hn1; reflexivity)
    eq_refl) as HS. clear HS0.
  pose proof (s1_shok ly S W mem md (s12_E regs (s1_extra b0 b1 b2)) (x_p cx) (x_n cx) 1 HAR Hin
    ltac:(rewrite (EE 5%nat 5%bv eq_refl); exact R5) ltac:(rewrite (EE 24%nat 24%bv eq_refl); exact R24)
    ltac:(lia) ltac:(lia)) as SHOK.
  remember (s12_E regs (s1_extra b0 b1 b2)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* 0x84eb8 .. 0x84f80: 24(s1) := FR; n <> 0; check 1, byte 0, mod40A, cap into 40(s1), s9 := 1; n = 1:
     s3 := FR, 16(s1) := 0, s4 := 0, s8 := p + 1; a0 := 16616, jal malloc *)
  paj_run_tok RUN HS HJ SHOK S12span.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0' ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0' bc fr ly0 own) end.
    eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia | |].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold STK_LLVMFuzzerTestOneInput. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  assert (U9' : bv_unsigned (ew E 9) = x_s1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia).
  pose proof (s1_kept E W mem (ms_mem ms) 1 (x_s1 cx) HFr U9') as KM.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (s1_slot _ _ _ _ _ 16 _ HM ltac:(left; reflexivity) ltac:(left; reflexivity)) as SL16.
  pose proof (s1_slot _ _ _ _ _ 40 _ HM ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as SL40.
  pose proof (s1_slot _ _ _ _ _ 24 _ HM ltac:(left; reflexivity) ltac:(right; right; left; reflexivity)) as SL24.
  cbn [YP09.r_base base_val] in SL16, SL40, SL24.
  repeat (rewrite ew_ewset_other in SL16, SL40, SL24 by lia).
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 21]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
        rewrite P; apply EE; reflexivity | ]).
    destruct Hr. }
  apply (s1_finish cx ly S W regs mem md acc (ms_regs ms) (ms_mem ms) md1 HK HB Hfrm HC HJ KM
    (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
    (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))).
  + rewrite P10. reflexivity.
  + exact P1.
  + rewrite P19, (EE 17%nat 17%bv eq_refl). exact R17.
  + rewrite P20. unfold w64. f_equal. unfold x_curn. rewrite Mcn. lia.
  + rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. rewrite YP03.unsigned_lit_small by lia.
    f_equal. unfold x_cur. rewrite Mca. lia.
  + rewrite P25. unfold w64. f_equal. unfold x_nf. rewrite Mnf, Hb2z. reflexivity.
  + rewrite (EE 9%nat 9%bv eq_refl), R9 in SL16, SL40, SL24.
    unfold w64 in SL16, SL40, SL24. rewrite YP03.unsigned_lit_small in SL16, SL40, SL24 by lia.
    intros o v Hio. cbn [In] in Hio. destruct Hio as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <-.
    * rewrite SL16. f_equal. rewrite U_lit by lia. unfold x_flags. rewrite Mfl, Hb1z. reflexivity.
    * rewrite SL24. f_equal. apply U_atom; [|unfold x_fr in *; lia].
      repeat (rewrite ew_ewset_other by lia). rewrite (EE 16%nat 16%bv eq_refl). exact R16.
    * rewrite SL40. f_equal. unfold x_cap. rewrite Mcap. apply s1_U_cap; [s1_atom | exact B0].
- (* ---- n = 2: two header bytes; s4 pinned to 2 ---- *)
  destruct Hpay as [[Hz _] | [Hrng Hin0]]; [lia|].
  assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
  { unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0. }
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
  pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
  assert (Rd0 : rdW W mem (x_p cx) = Some b0).
  { rewrite <- (Z.add_0_r (x_p cx)). apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 0%nat). lia. }
  assert (Rd1 : rdW W mem (x_p cx + 1) = Some b1)
    by (apply (s1_pay cx ly S W regs mem md 0 acc _ LFO0 [] HB HC ltac:(lia) 1%nat); lia).
  assert (Hb2z : b2 = 0) by (unfold b2, seg_spec.seg_in, seg_spec.zs; apply nth_overflow; rewrite length_map; lia).
  assert (Hd2 : x_p cx + 2 <= mod40A \/ mod40A + 8 <= x_p cx).
  { destruct (Z_le_gt_dec (x_p cx + 2) mod40A) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (mod40A + 8) (x_p cx)) as [H'|H']; [right; exact H'|]. exfalso.
    destruct (Hm40i (Z.max (x_p cx) mod40A) ltac:(lia)) as (Himg & _).
    assert (Hblk : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= Z.max (x_p cx) mod40A < p0 + req_size n0)
      by (exists (x_p cx), (x_n cx); split; [exact Hin | lia]).
    exact (proj2 (al_client_img _ _ LAWS ly S W mem md (Z.max (x_p cx) mod40A) HAR (or_introl Hblk)) Himg). }
  pose proof (s1_seed 2 2 2 W regs mem b0 b1 b2 (x_p cx) (x_s1 cx) ltac:(lia) R5 R9 R24 Hs1r Hs1al
    ltac:(lia) ltac:(lia) B0 B1 B2 (fun _ => Rd0) (fun _ => Rd1) ltac:(intros Hc; exfalso; lia)
    HSLW Hm40 HV4 ltac:(lia) Hd2 Hd3) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ 20%bv 2 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite R20, Hn2; reflexivity)
    eq_refl) as HS. clear HS0.
  pose proof (s1_shok ly S W mem md (s12_E regs (s1_extra b0 b1 b2)) (x_p cx) (x_n cx) 2 HAR Hin
    ltac:(rewrite (EE 5%nat 5%bv eq_refl); exact R5) ltac:(rewrite (EE 24%nat 24%bv eq_refl); exact R24)
    ltac:(lia) ltac:(lia)) as SHOK.
  remember (s12_E regs (s1_extra b0 b1 b2)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* 0x84eb8 .. 0x84f80: 24(s1) := FR; n <> 0; check 1, byte 0, mod40A, cap into 40(s1), s9 := 1; n <> 1;
     check 2, byte 1 into 16(s1); n = 2: s3 := FR, s4 := 0, s8 := p + 2; a0 := 16616, jal malloc *)
  paj_run_tok RUN HS HJ SHOK S12span.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0' ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0' bc fr ly0 own) end.
    eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia | |].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold STK_LLVMFuzzerTestOneInput. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  assert (U9' : bv_unsigned (ew E 9) = x_s1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia).
  pose proof (s1_kept E W mem (ms_mem ms) 2 (x_s1 cx) HFr U9') as KM.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (s1_slot _ _ _ _ _ 16 _ HM ltac:(left; reflexivity) ltac:(left; reflexivity)) as SL16.
  pose proof (s1_slot _ _ _ _ _ 40 _ HM ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as SL40.
  pose proof (s1_slot _ _ _ _ _ 24 _ HM ltac:(left; reflexivity) ltac:(right; right; left; reflexivity)) as SL24.
  cbn [YP09.r_base base_val] in SL16, SL40, SL24.
  repeat (rewrite ew_ewset_other in SL16, SL40, SL24 by lia).
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 21]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
        rewrite P; apply EE; reflexivity | ]).
    destruct Hr. }
  apply (s1_finish cx ly S W regs mem md acc (ms_regs ms) (ms_mem ms) md1 HK HB Hfrm HC HJ KM
    (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
    (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))).
  + rewrite P10. reflexivity.
  + exact P1.
  + rewrite P19, (EE 17%nat 17%bv eq_refl). exact R17.
  + rewrite P20. unfold w64. f_equal. unfold x_curn. rewrite Mcn. lia.
  + rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. rewrite YP03.unsigned_lit_small by lia.
    f_equal. unfold x_cur. rewrite Mca. lia.
  + rewrite P25. unfold w64. f_equal. unfold x_nf. rewrite Mnf, Hb2z. reflexivity.
  + rewrite (EE 9%nat 9%bv eq_refl), R9 in SL16, SL40, SL24.
    unfold w64 in SL16, SL40, SL24. rewrite YP03.unsigned_lit_small in SL16, SL40, SL24 by lia.
    intros o v Hio. cbn [In] in Hio. destruct Hio as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <-.
    * rewrite SL16. f_equal. unfold x_flags. rewrite Mfl. apply s1_U_ext8; [s1_atom | exact B1].
    * rewrite SL24. f_equal. apply U_atom; [|unfold x_fr in *; lia].
      repeat (rewrite ew_ewset_other by lia). rewrite (EE 16%nat 16%bv eq_refl). exact R16.
    * rewrite SL40. f_equal. unfold x_cap. rewrite Mcap. apply s1_U_cap; [s1_atom | exact B0].
Qed.
End e.
End f.
End d.
